#requires -Version 5
# cut-releases.ps1 — publish NetTopologySuite.Proofs package releases.
# Triggers the package-*.yml workflows (build + attach tarball + opam publish).
# Needs the GitHub CLI (gh), authenticated (gh auth login) or GITHUB_TOKEN set.
$ErrorActionPreference = 'Stop'

$repo = 'grootstebozewolf/NetTopologySuite.Proofs'

$releases = @(
  @{ Tag='spatial-algebra-v0.1.3';   Title='coq-spatial-algebra 0.1.3';   Notes='Axiom-free DE-9IM algebra + integer determinant bounds.' }
  @{ Tag='robust-predicates-v0.1.2'; Title='coq-robust-predicates 0.1.2'; Notes='Robust binary64 geometric predicates, sound vs. exact arithmetic.' }
)

if (-not (Get-Command gh -ErrorAction SilentlyContinue)) {
  throw "GitHub CLI 'gh' not found. Install from https://cli.github.com/ then run 'gh auth login'."
}

foreach ($r in $releases) {
  # If a draft/release with this tag already exists, remove it first so the
  # create (and the publish trigger) is clean. Ignore errors if it doesn't exist.
  gh release delete $r.Tag --repo $repo --yes --cleanup-tag 2>$null

  Write-Host "Publishing $($r.Tag) on main ..." -ForegroundColor Cyan
  gh release create $r.Tag --repo $repo --target main --title $r.Title --notes $r.Notes
  if ($LASTEXITCODE -ne 0) { throw "gh release create failed for $($r.Tag) (exit $LASTEXITCODE)" }
  Write-Host "  -> https://github.com/$repo/releases/tag/$($r.Tag)" -ForegroundColor Green
}

Write-Host "Done. The publish workflows are now running for each tag." -ForegroundColor Green
