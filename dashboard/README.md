# Observatory dashboard

A single-page **status view of this proof corpus**, generated entirely from
in-repo source of record:

| Source | Feeds |
|---|---|
| `docs/verified-claims.md` | cited-theorem totals + regime mix (per area) |
| `TRIAGE_NTS_JTS_ISSUES.md` | per-issue (#64–#69) priority + verdict |
| `oracle/*_vectors.txt`, `*_tests.txt` | differential oracle modes + vector counts |
| `docs/admitted-counterexamples.txt`, `docs/admitted-deferred-proofs.txt` | Admitted registry footprint |
| `docs/oracle-handrolled-allowlist.txt` | frozen interface-boundary kernels |

## What it is — and isn't

This corpus is the **soundness oracle / reference** for the JTS → NTS stack.
The dashboard reports *what is formally proven here* and *which extracted
oracle vectors back it*, and deep-links out to JTS and NTS. It is **not** a
JTS/NTS test runner — the cross-project differential harness lives downstream
in `NetTopologySuite.Curve`. The page deliberately keeps the corpus's
`proven` / `conditional` / `oracle` distinctions explicit; there is no
flattened "all green" health score.

## Regenerate locally

```sh
python3 scripts/gen_dashboard.py        # writes dashboard/index.html
python3 scripts/gen_dashboard.py --check # CI-style staleness check
```

No dependencies beyond the Python standard library; the output is a single
self-contained HTML file (inline CSS, no CDN).

## Publishing

`.github/workflows/pages.yml` regenerates and deploys to GitHub Pages on every
push to `main` touching the inputs above. One-time setup: **Settings → Pages →
Source = "GitHub Actions"**. The committed `index.html` is a generated preview
so the page is viewable directly in the repo too.
