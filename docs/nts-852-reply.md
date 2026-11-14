<!-- doc-kind: finding
date: 2026-08-17
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Paste-ready reply for [NTS #852](https://github.com/NetTopologySuite/NetTopologySuite/pull/852)

The GitHub token on this lane cannot comment on `NetTopologySuite/NetTopologySuite` (403). Someone with write access should paste the block below on #852.

---

@bjornharrtell

"Oracle" in the earlier notes was the old `RocqRefRunner` subprocess name, not a production default. If #852 stays the small defensive-copy PR, we can strip that wording there. The copies themselves are the point.

We are not waiting on locationtech/jts or dr-jts. Java is greenfield on the fork SoT:

- [grootstebozewolf/jts#7](https://github.com/grootstebozewolf/jts/pull/7) (`feature/sfa-curve-rgr`)
- stacked Phase 5 Java PR: [grootstebozewolf/jts#64](https://github.com/grootstebozewolf/jts/pull/64)

GEOS sibling: [grootstebozewolf/geos#2](https://github.com/grootstebozewolf/geos/pull/2)

#852 should stay NTS copies + pins only. Phase 5 in-process `libntsrocq` is a separate Lab PR: [grootstebozewolf/NetTopologySuite#7](https://github.com/grootstebozewolf/NetTopologySuite/pull/7). Core `RobustLineIntersector` defaults stay on the stock path.

Bindings + ABI: [NetTopologySuite.Proofs#485](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/pull/485), `oracle/CONSUMERS.md`.

The JTS `RocqRefRunner.refSign` integer algorithm (not the subprocess, not production DD) now has a Qed proof that it is the exact `cross` sign, plus a C# port on NTS that loads the same vectors: `docs/rocqref-jts-nts-equiv.md`.
