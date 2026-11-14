<!-- doc-kind: guide -->
# Archived Java intake (not primary)

The Java visitor (`org.nts.proofs.intake`) and bash `generate.sh` /
`smoke.sh` were the first-slice primary. House style is now
**.NET / PowerShell / Cake** in the parent directory.

These files stay as a behaviour pin / archaeology only. Do not
document them as the smoke entry. Grammar pin is unchanged
(`../grammar/`, `../PIN.md`).

To replay the retired path (needs JDK + the ANTLR complete jar):

```
bash tools/WktIntakeWalker/archive/generate.sh
bash tools/WktIntakeWalker/archive/smoke.sh
```

`archive/generate.sh` writes into `archive/java/org/nts/proofs/intake/gen/`
(gitignored).
