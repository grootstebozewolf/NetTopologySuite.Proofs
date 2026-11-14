<!-- doc-kind: finding
date: 2026-08-05
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# FFI rungs — restore full `libntsrocq` + orientation lane (2026-08)

**Date**: 2026-08-05.  
**topic:** `precision` / `docs` · epics **#66** (orient), Phase 5 FFI.  
**Trigger**: Mesh in-circle sessions used a scout-only library because workspace
`extracted.ml` was stale (missing `b64_orient2d_exact`). Next JTS picks
(#1093 Ozaki, #1197 DD characterization) need **filtered + exact** orient in
process — not new ABI symbols.

**Product call from scout**: expand **ergonomics**, not surface area
([jts-open-prs-scout-2026-08.md](jts-open-prs-scout-2026-08.md)).

---

## §0 — Rung ladder

| Rung | Goal | Status (2026-08-05) |
|---|---|---|
| **0** | Document gap + rebuild path | **This doc** |
| **1** | Re-extract `Validate_binary64_extract.v` → freshen `oracle/extracted.ml` | **GREEN** (local WSL; extract is gitignored) |
| **2** | `make -C oracle ffi` → full `libntsrocq.so` + `ffi_probe` | **GREEN** after rung 1 |
| **3** | `make -C oracle ffi-parity` | **YELLOW** — 3 ORIENT_EXACT* cases segfault on extreme coords (see §3) |
| **4** | Orientation differential scout for [jts#1093](https://github.com/locationtech/jts/pull/1093) | **GREEN** — 45 vectors; see [`jts-1093-orient-lane-2026-08.md`](jts-1093-orient-lane-2026-08.md) |
| **5** | Retire / demote `scout_incircle_*` once full FFI is the default path | Pending CI green on parity |
| **6** | Optional: post numbers on jts#1093 / keep #1197 green | #1197 keep-green **done** 2026-08-05 (rebase + vectors + [merge ping](https://github.com/locationtech/jts/pull/1197#issuecomment-5186644725)); #1093 draft: `tests/Discussion839Mre/jts-1093-comment.md` |

---

## §1 — Root cause of the scout fork

`oracle/nts_ffi.ml` registers `orient_sign_exact` → `b64_orient2d_exact`.  
`theories-flocq/Validate_binary64_extract.v` **lists** that symbol in the
`Extraction` command, but a workspace `extracted.ml` produced without a
fresh Flocq extract omits it → `make -C oracle ffi` fails with
`Unbound value b64_orient2d_exact`.

Mesh session 2 therefore shipped `scout_incircle_ffi.ml` (in-circle only).
That was correct as a temporary path; it is **not** the long-term Phase 5
story.

---

## §2 — Rebuild (rungs 1–2)

Extract is **gitignored**. Rebuild on a Linux/WSL host with Rocq + Flocq and
compiled `.vo` for the extract dependency closure:

```bash
# From repo root (Rocq 9.x + Flocq; theories-flocq/*.vo present):
coqc -Q theories NTS.Proofs -Q theories-flocq NTS.Proofs.Flocq \
  theories-flocq/Validate_binary64_extract.v

make -C oracle          # oracle_bin
make -C oracle ffi      # libntsrocq.so + ffi_probe
make -C oracle ffi-parity
```

Helper script (best-effort): [`scripts/rebuild_oracle_ffi.sh`](../scripts/rebuild_oracle_ffi.sh).

Smoke (exact escalation + filter + in-circle):

```bash
printf '0 0\n1 0\n0 1\n' | oracle/ffi_probe ORIENT_EXACT          # → 1 (POS)
printf '0 0\n1 0\n0 1\n' | oracle/ffi_probe ORIENT_FILTERED       # → 1 #...
printf '0 0\n2 0\n1 1\n1 -0.5\n' | oracle/oracle_bin               # mode on stdin first
# INCIRCLE_SIGN via oracle_bin (ffi_probe mode name is INCIRCLE_SIGN):
printf '0 0\n2 0\n1 1\n1 -0.5\n' | oracle/ffi_probe INCIRCLE_SIGN
```

---

## §3 — Parity result (rung 3)

Local run after re-extract (2026-08-05, ~1215 cases):

| Mode | Result |
|---|---|
| ORIENT_FILTERED / ORIENT | OK |
| INTERSECT_* / PASSES_* / SNAP / EDGE / INCIRCLE / ARC / TWOSUM / GROW / SIMPLIFY | OK |
| **ORIENT_EXACT** | **1 MISMATCH** (FFI side errored) |
| **ORIENT_EXACT_EXTRACTED** | **2 MISMATCH** (FFI side errored) |

**Failure shape:** `ffi_probe ORIENT_EXACT` **segfaults** on at least one
adversarial input with mixed subnormal / near-overflow coordinates, e.g.:

```text
0x0.0p+0  0x0.0p+0
0x0.0000000000001p-1022  0x0.0000000000001p-1022
0x1.1ccf385ebc8a0p+1023  0x1.1ccf385ebc8a0p+1023
```

`oracle_bin` `ORIENT_EXACT` / extracted path still answers (`ZERO` / `NEG`).
So the bug is **in-process Callback / runtime path** (stack, GC, or Z
allocation under the shared-lib runtime), not the abstract algorithm.

**Policy until fixed:**

- Use **`oracle_bin` ORIENT_EXACT** as ground truth for #1093 / #1197 scouts.
- Use **FFI** for filtered/naive/in-circle/snap (parity green).
- Do **not** claim full-plane exact FFI for production escalation until the
  segfault class is gone or bounded out of the contract.

---

## §4 — Orientation lane (rung 4) — GREEN

Upstream: [jts#1093](https://github.com/locationtech/jts/pull/1093) replaces
JTS `orientationIndexFilter` Shewchuk-ish / `DP_SAFE_EPSILON=1e-15` path with
**Ozaki et al.** permanent-style bound:

```text
detleft  = (pax - pcx) * (pby - pcy)
detright = (pay - pcy) * (pbx - pcx)
det      = detleft - detright
errbound = |detleft + detright| * 3.3306690621773724e-16
certain  iff |det| >= errbound
```

Corpus counterpart:

| Asset | Role |
|---|---|
| `b64_orient_sign_filtered` | Shewchuk Stage A (corpus / FFI) |
| `b64_orient2d_exact` / `ORIENT_EXACT` | Full-plane sign GT |
| `oracle/gen_jts1093_orient_scout.py` | Three-way: master / Ozaki / Shewchuk vs exact |
| [`jts-1093-orient-lane-2026-08.md`](jts-1093-orient-lane-2026-08.md) | Session write-up |

**Gate (2026-08-05, 45 vectors):** Ozaki / Shewchuk / master CERTAIN vs exact
conflicts all **0**. Ozaki CERTAIN while master UNCERTAIN: **4** (same-sign
\(h \in \{10^{-15}, 2\cdot10^{-15}\}\) band). Ozaki ↔ corpus Shewchuk certainty
splits: **0**. Details and PR comment draft in the lane doc.

---

## §5 — What not to do

- Do **not** add Ozaki as a Rocq FFI entry until/unless the corpus proves an
  Ozaki filter (product decision + claimId). Differential scouts mirror in Python.
- Do **not** dual-track scout + full lib in CI forever — pick full lib after
  exact-FFI is fixed or explicitly excluded from parity.
- Do **not** invent claimId for history/scout scripts (ADR-0004 cold).

---

## §6 — Next actions

1. Track ORIENT_EXACT FFI segfault (rung 3 close-out) — isolated repro above.
2. ~~Run `python3 oracle/gen_jts1093_orient_scout.py`~~ **done** (rung 4 GREEN);
   optional: post `tests/Discussion839Mre/jts-1093-comment.md` on jts#1093.
3. Wire `make -C oracle ffi` into developer docs / optional CI once parity is
   green or exact is skipped under a named env flag.

**AI assistance**: Grok (grok-4.5), human-directed.  
**License**: project documentation (BSD-3-Clause).
