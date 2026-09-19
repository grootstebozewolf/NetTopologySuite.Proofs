# Karney 2013 · Algorithms for geodesics — research ingest

claimId: 0007-karney-2013-ingest · board: ADR-0007 · kind: research · source: Karney CFF, J Geod 87:43–55 (2013), doi 10.1007/s00190-012-0578-z, open access (CC-BY, p. 54) · PDF sha256 1eb833d9acf94d03d94a7b8237971c881ad946ea9d3af3e00b739f7826ccf0f1 · Coq: `IntakeKarneyPark.v`. AI-drafted, human-reviewed.

This is a research letter on an ellipsoid of revolution, not a cook, not a first-cook expand, not `MkGeodesic`. It is not the planar geodesic machine of #788 (`IntakeGeodesicCook.v`: sheet chord = geodesic on S = (O; e1, e2)); #788 is not on main at the time of writing, so nothing here says "geodesic closed".

## Facts from the article (page-cited, 2013 pagination)

1. **Problems.** Direct: given φ₁, α₁, s₁₂, find the end point. Inverse: given φ₁, λ₁₂, φ₂, find the shortest path. Each is the geodesic triangle NAB given two sides and the included angle (α₁ direct, λ₁₂ inverse) (p. 43; restated p. 54 Sect. 9 with sides φ₁, φ₂, s₁₂ and angles α₁, α₂, λ₁₂).
2. **Lineage.** Framework laid down by Legendre (1806), Oriani (1806, 1808, 1810), Bessel (1825), Helmert (1880); Vincenty (1975a) devised algorithms "suitable for early programmable desk calculators; these algorithms are in widespread use today"; Rapp (1993, Chap. 1) is the summary of Vincenty and the earlier work (p. 43).
3. **Beyond Vincenty, three ways** (p. 43): (1) accuracy raised to "the standard precision of most computers" by retaining series terms; (2) an inverse solution "which converges for all pairs of points (Vincenty's method fails to converge for nearly antipodal points)"; (3) differential and integral properties: reduced length m₁₂, geodesic scale M₁₂ (p. 47), and the area of a geodesic polygon.
4. **Inverse near antipodes.** Vincenty (1975a) uses Helmert's iteration and "was aware of its failure to converge for nearly antipodal points"; the unpublished Vincenty (1975b) modifies it but "sometimes requires many thousands of iterations", against a few Newton iterations here (p. 49). Vincenty's inverse "sometimes fails to converge" (p. 53). Karney: "this paper presents the first complete solution to the inverse geodesic problem" (p. 54).
5. **Auxiliary sphere.** Ellipsoid of revolution with a, b, f, n, e, e′ (p. 44 Eqs. 1–4); Clairaut sin α₀ = sin α₁ cos β₁ = sin α₂ cos β₂ with reduced latitude tan β = (1 − f) tan φ (p. 44 Eqs. 5–6); the sphere keeps azimuths and swaps φ for β. Because Eqs. 7–8 depend on α₀, the mapping "is not a global mapping of one surface to another" and only longitude differences λ₁₂ should be used (p. 45).
6. **Integrals.** s/b = I₁(σ) and λ = ω − f sin α₀ I₃(σ), k = e′ cos α₀ (p. 44 Eqs. 7–9); Fourier series I₁ = A₁(σ + Σ C₁ₗ sin 2lσ), I₃ = A₃(σ + Σ C₃ₗ sin 2lσ) in the parameter ε = (√(1+k²) − 1)/(√(1+k²) + 1) rather than k², giving "half as many terms" (p. 45 Eqs. 15–16, 23).
7. **Bibliography (p. 55).** Vincenty T (1975a) Direct and inverse solutions of geodesics on the ellipsoid with application of nested equations. Surv Rev 23(176):88–93 [addendum: Surv Rev 23(180):294 (1976)]. Vincenty T (1975b) Geodetic inverse solution between antipodal points. http://geographiclib.sf.net/geodesic-papers/vincenty75b.pdf (unpublished report dated Aug 28).
8. **What it is not.** Not a plane-sheet geodesic, not SQL/MM GEODESICSTRING, not WKB 13, not an NTS/JTS cook: the article's geodesic is straightness κ = 0 on the ellipsoid surface (p. 44) and its inverse is a root-finding exercise by Newton's method (p. 48); none of those objects appears on pp. 43–55.

## Tickets (`IntakeKarneyPark.v`, no third status)

| Ticket | Close | Lemma |
|---|---|---|
| K0 not planar intake | **QED** — GEODESICSTRING μ stays `MkChord` on every ADR-0007 `Sheet`; NAB is not that bag | `IntakeKarneyPark.v : ticket_0007_karney_not_planar_intake_qed_or_qex` |
| K1 Vincenty inverse not total | **QEX** — not implemented here; failure is Karney's claim (pp. 43, 49, 53), not a corpus counterexample | `IntakeKarneyPark.v : ticket_0007_karney_vincenty_total_qed_or_qex` |
| K2 ellipsoid geodesic ≠ sheet chord | **QEX** — a chord-hit statement, not an inverse result: the closed term is `on_chord` membership of the G3 pole (`IntakeGeodesicCook.v : sheet_chord_misses_pole`), planar chord geometry on ADR-0007 Sheet S; it says nothing about Karney's inverse problem (f(α₁) = λ₁₂(α₁) − λ★, m₁₂, Vincenty 1975a/b, Newton). The inverse is K1. G3 not reminted | `IntakeKarneyPark.v : ticket_0007_karney_chord_not_geodesic_qed_or_qex` |
| K3 new sheet class | **QEX** — an ellipsoid sheet does not inhabit ADR-0007 `Sheet` = (O; e1, e2); a new ADR is required | `IntakeKarneyPark.v : ticket_0007_karney_new_sheet_class_qed_or_qex` |

Not claimed: that the corpus solves the inverse geodesic problem. Karney is a named park (ambient ellipsoid), not a discharge of G3. ADR-0007 stays Accepted.
