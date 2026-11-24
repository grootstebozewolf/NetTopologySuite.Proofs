<!-- doc-kind: guide -->
# Literature map — board cards → papers (2026-11)

**Purpose.** Targeted research assistance: for each open / red / HOLD card on
the NTS RGR Board, the papers that give a concrete oracle test, proof target
or honesty boundary. Drop the PDF in the session (as with H-IMPRECISE) to turn
an entry into a hunt.

**Provenance.** Compiled 2026-11-24 by three web-search passes. DOIs were
checked against Crossref / publisher / DBLP / HAL / arXiv unless marked
*(unverified)*. The 27 DOIs already cited in `docs/` and `theories/` were
excluded. Nothing here is a verified claim; entries are leads.

**Legend.** ★ = read first for that card. OA = open-access copy.

---

## H-IMPRECISE — Hausdorff between imprecise points (discs)
Anchor: Knauer, Löffler, Scherfenberg, Wolle, TCS 412 (2011), 10.1016/j.tcs.2011.01.039.

| | Paper | DOI | Targeted use |
|---|---|---|---|
| ★ | Löffler & van Kreveld, *Largest bounding box, smallest diameter… imprecise points*, WADS 2007 / CGTA 43(4) 2010 | 10.1007/978-3-540-73951-7_39 (CGTA DOI unverified) · OA: Utrecht TR CS-2007-025 | Closed-form max/min bbox and diameter over discs → direct CIRCLE oracle |
| | Löffler, *Data Imprecision in Computational Geometry*, PhD Utrecht 2009 | ISBN 978-90-8891-121-7 · OA dspace.library.uu.nl | Model spec for a disc-imprecise point in Rocq |
| | Ahn, Knauer, Scherfenberg, Schlipf, Vigneron, *Discrete Fréchet with imprecise input*, IJCGA 22(1) 2012 | 10.1142/S0218195912600023 | Lower/upper bound pairs for disc-vertex polylines (ref [1] of anchor) |
| | Löffler & Snoeyink, *Delaunay of imprecise points in linear time after preprocessing*, CGTA 43(3) 2010 | 10.1016/j.comgeo.2008.12.007 | Metamorphic test: result = plain Delaunay of chosen points |
| | Buchin, Fan, Löffler, Popov, Raichel, Roeloffzen, *Fréchet distance for uncertain curves*, ACM TALG | 10.1145/3597640 · arXiv 2004.11862 | Bounds for curves with disc vertices; NP-hardness = what not to promise |

## M.1 / D-HF — DirectedHausdorff on Curve*
| | Paper | DOI | Targeted use |
|---|---|---|---|
| ★ | Alt & Scharf, *Computing the Hausdorff distance between curved objects*, IJCGA 18(4) 2008 | 10.1142/S0218195908002647 | Finite candidate set for arcs/algebraic curves → Rocq theorem "arc Hausdorff attained on finite set"; lifts the two-pair D-HF lock |
| | Alt, Behrends, Blömer, *Approximate matching of polygonal shapes*, AMAI 13 1995 | 10.1007/BF01530830 · OA core.ac.uk/download/199414746.pdf | Segment-set Hausdorff via Voronoi candidates — the linear lemma first (ref [2] of anchor) |
| | Kim, Oh, Yoon, Kim, Elber, *Precise Hausdorff for planar freeform curves using biarcs*, Vis. Comput. 26 2010 | 10.1007/s00371-010-0477-3 | Its arc-vs-arc kernel = exact oracle on CIRCULARSTRING pairs |
| | Elber & Grandine, *Hausdorff and minimal distances between parametric freeforms*, GMP 2008 | 10.1007/978-3-540-79246-8_15 · OA gershon.cs.technion.ac.il | Antipodal / bisector conditions; worked examples as fixtures |
| | Bai et al., *Polyline approach for approximating Hausdorff…*, CAD 43(6) 2011 | (unverified) | The chord baseline the no-chord-lie rule is measured against |

## #423 — Fréchet for arcs
| | Paper | DOI | Targeted use |
|---|---|---|---|
| ★ | Rote, *Fréchet distance between piecewise smooth curves*, CGTA 37 2007 | 10.1016/j.comgeo.2005.01.004 | Arc–arc free-space cell = oracle kernel |
| | Alt & Godau, *Fréchet distance between two polygonal curves*, IJCGA 5 1995 | 10.1142/S0218195995000064 (unverified landing) | Free-space cell convexity lemma |
| | Conradi, Driemel, Kolbe, *Revisiting Fréchet between piecewise smooth curves*, EuroCG 2024 | arXiv 2401.03339 | Simplest decision procedure to port to arcs |
| | Bringmann, *Why walking the dog takes time*, FOCS 2014 | arXiv 1404.1448 | Complexity ceiling: never claim subquadratic |

## CRV-NODING / OV-NODING — arc arrangements
| | Paper | DOI | Targeted use |
|---|---|---|---|
| ★ | Berberich, Eigenwillig, Hemmer, Hert, Mehlhorn, Schömer, *Conic arcs and Boolean ops on conic polygons*, ESA 2002 | 10.1007/3-540-45749-6_19 · OA uni-mainz ESA02.pdf | Exact kernel + sweep; degenerate inputs (tangent arcs, crossing at x-extreme) as noding tests. Also serves PRF-ELLIPSE |
| | Eigenwillig & Kerber, *Exact 2D arrangements of arbitrary algebraic curves*, SODA 2008 | 10.1145/1347082.1347096 · OA TU Graz | Split arcs at x-extremes → noding spec |
| | Wein, *High-level filtering for arrangements of conic arcs*, ESA 2002 | 10.1007/3-540-45749-6_76 | Proof target: certified filter agrees with exact predicate |
| | Emiris, Kakargias, Pion, Teillaud, Tsigaridas, *Towards an open curved kernel*, SoCG 2004 | (unverified) · OA HAL inria-00344433 | CGAL circular-kernel predicate checklist |

## CRV-TOUCH — exact tangency (spec merged #1038; follow-up for noder)
| | Paper | DOI | Targeted use |
|---|---|---|---|
| ★ | Devillers, Fronville, Mourrain, Teillaud, *Exact predicates on circle arcs*, CGTA 22 2002 | 10.1016/S0925-7721(01)00050-5 · OA HAL inria-00072832 | Degree-≤12 resultants → static Flocq filter bound; double-root = kiss test |
| | Emiris & Tsigaridas, *Comparing real algebraic numbers of small degree*, ESA 2004 | 10.1007/978-3-540-30140-0_58 · arXiv cs/0512072 | Branch-free √-expression comparison. Also PRF-ELLIPSE (quartic) |

## CRV-SNAP — snapping curves
| | Paper | DOI | Targeted use |
|---|---|---|---|
| ★ | Eigenwillig, Kettner, Wolpert, *Snap rounding of Bézier curves*, SoCG 2007 | (unverified) · TR MPI-I-2006-1-005 | "May collapse, never invert" → acceptance clause for arc snapping |
| | Hershberger, *Stable snap rounding*, CGTA 46(4) 2013 | 10.1016/j.comgeo.2012.02.011 | Idempotence oracle SR(SR(x)) = SR(x) |
| | Hershberger, *Snap rounding: a cautionary tale*, SoCG 2025 | 10.4230/LIPIcs.SoCG.2025.57 (OA) | Failure modes → attack tickets |
| | Halperin & Packer, *Iterated snap rounding*, CGTA 23(2) 2002 | 10.1016/S0925-7721(01)00064-5 | Drift examples as SnapRoundingNoder regressions |
| | Guibas & Marimont, *Rounding arrangements dynamically*, IJCGA 8(2) 1998 | 10.1142/S0218195998000096 | Segment invariants as baseline lemmas |

**Gap (open ground):** no peer-reviewed snap rounding specific to circular arcs found.

## PRF-P7 — overlay soundness audit
| | Paper | DOI | Targeted use |
|---|---|---|---|
| ★ | Kettner, Mehlhorn, Pion, Schirra, Yap, *Classroom examples of robustness problems*, CGTA 40(1) 2008 | (unverified; believed 10.1016/j.comgeo.2007.06.003) · OA cs.nyu.edu/~exact/doc/classroom.pdf | Replay published float failures against the oracle |
| | Hachenberger, Kettner, Mehlhorn, *Boolean ops on 3D selective Nef complexes*, CGTA 38 2007 | (unverified) | Regularized-overlay semantics incl. boundary-only results |
| | Lévy, *Exact predicates, constructions and combinatorics for mesh CSG*, ACM TOG 2025 | 10.1145/3744642 (aggregator only) · arXiv 2405.12949 | Recent exact-overlay pipeline; thingiCSG benchmark |

**Gap:** no 2020–2026 paper on exact Boolean ops for circular-arc polygons.

## QG-CURVE-CHORD — certified arc ↔ polyline
| | Paper | DOI | Targeted use |
|---|---|---|---|
| ★ | Drysdale, Rote, Sturm, *Polygonal curve → minimum circular arcs/biarcs*, CGTA 41 2008 | 10.1016/j.comgeo.2007.10.009 | Polyline → arcs within tolerance (the reverse direction oracle) |
| | Park, *Error-bounded biarc approximation*, CAD 2004 | 10.1016/j.cad.2004.01.001 | Certified Hausdorff tolerance |
| | Held & Eibl, *Biarc approximation within asymmetric tolerance bands*, CAD 37(4) 2005 | (unverified) | One-sided bands → conservative containment |

Chord sagitta r·(1 − cos(θ/2)) has no citable paper; prove it directly in Rocq.

## Formal geometry (cross-cutting)
| | Paper | DOI | Targeted use |
|---|---|---|---|
| ★ | Melquiond & Pion, *Formally certified floating-point filters for homogeneous predicates*, RAIRO-ITA 41(1) 2007 | 10.1051/ita:2007005 · OA HAL inria-00071232 | Extend to circle-arc predicates (CRV-TOUCH) |
| | Brun, Dufourd, Magaud, *Convex hull with hypermaps in Coq*, CGTA 45(8) 2012 | 10.1016/j.comgeo.2010.06.006 · OA HAL hal-00955400 | Hypermap invariants for overlay planar graph |
| | Pichardie & Bertot, *Formalizing convex hull algorithms*, TPHOLs 2001 | 10.1007/3-540-44755-5_24 | Degeneracy handling template |
| | Bertot, *Abstract views and symmetry in Coq proofs*, ICTAC 2018 | 10.1007/978-3-030-02508-3_1 · arXiv 1809.00559 | Symmetry tactics to cut arc–segment case splits |

## ML.4 / ML.1 — MIC / medial axis with arcs
| | Paper | DOI | Targeted use |
|---|---|---|---|
| ★ | Held & Huber, *Voronoi of circular arcs and segments*, CAD 41(5) 2009 | 10.1016/j.cad.2008.08.004 · OA sthu.org HeHu09.pdf | Max-clearance Voronoi node = MIC; topology-first robustness rules |
| | Aichholzer et al., *Medial axis for planar free-form shapes*, CAD 41(5) 2009 | 10.1016/j.cad.2008.08.008 (single listing) · OA TU Graz | Arc-bounded medial axis |
| | Kim, Kim, Sugihara, *Voronoi of circle set from point Voronoi*, ISAAC 2000 | 10.1007/3-540-40996-3_37 | Disc-site test cases |

## JTS-1159 — minimum enclosing triangle
| | Paper | DOI | Targeted use |
|---|---|---|---|
| ★ | O'Rourke, Aggarwal, Maddila, Baldwin, *Optimal algorithm for minimal enclosing triangles*, J. Algorithms 7(2) 1986 | 10.1016/0196-6774(86)90007-6 | Side-midpoint touches polygon → invariant check on JTS output |
| | Chandran & Mount, *Parallel algorithm for enclosed and enclosing triangles*, IJCGA 2(2) 1992 | 10.1142/S0218195992000123 | Independent second oracle |

## PRF-ELLIPSE — elliptic arc
| | Paper | DOI | Targeted use |
|---|---|---|---|
| ★ | Emiris, Tsigaridas, Tzoumas, *Predicates for the Voronoi diagram of ellipses*, SoCG 2006 / IJCGA 2008 | 10.1145/1137856.1137891 · 10.1142/S0218195908002763 | InCircle / side-of-bisector for ellipses, bounded degree |
| | Carlson, *Numerical computation of real or complex elliptic integrals*, Numer. Algorithms 10 1995 | 10.1007/BF02198293 · arXiv math/9409227 | Certified elliptic arc length (explicit truncation bounds) |
| | Johansson, *Numerical evaluation of elliptic functions/integrals*, 2019 | arXiv 1806.06725 | Arb ball enclosures as reference values |
| | (+ Berberich et al. 2002, Wein 2002, Emiris–Tsigaridas 2004 above) | | |

## PRF-BEZIER — cubic Bézier
| | Paper | DOI | Targeted use |
|---|---|---|---|
| ★ | Mainar & Peña, *Error analysis of corner cutting algorithms*, Numer. Algorithms 22 1999 | 10.1023/A:1019190220312 | de Casteljau (and de Boor) error bounds → Flocq lemma |
| | Sederberg & Nishita, *Curve intersection using Bézier clipping*, CAD 22(9) 1990 | 10.1016/0010-4485(90)90039-F | Paper examples as intersection oracle cases |
| | Delgado & Peña, *Running relative error for polynomial evaluation*, SISC 31(5) 2009 | 10.1137/080745249 | Sharp running bounds; reproducible experiments |
| | Hermes, *Compensated de Casteljau in K× working precision*, AMC 357 2019 | 10.1016/j.amc.2019.03.047 · arXiv 1808.10387 | EFT evaluator with proved bound |
| | Schulz, *Bézier clipping is quadratically convergent*, CAGD 26(1) 2009 | 10.1016/j.cagd.2007.12.006 (weak) | Iteration bound |

## CRV-CLOTHOID
Note: Bertolazzi & Frego G1 fitting (10.1002/mma.3114) is already cited.

| | Paper | DOI | Targeted use |
|---|---|---|---|
| ★ | Alazah, Chandler-Wilde, La Porte, *Fresnel integrals via modified trapezium rules*, Numer. Math. 128(4) 2014 | 10.1007/s00211-014-0627-z · arXiv 1209.3451 | Rigorous C(x)/S(x) bounds → certified Fresnel |
| | Frego & Bertolazzi, *Point-clothoid distance and projection*, SISC 41(5) 2019 | 10.1137/18M1200439 | Clothoid distance oracle. A 2026 arXiv note reportedly disputes its single-minimum assumption (unverified) → possible attack ticket |
| | Bertolazzi & Frego, *G2 Hermite interpolation with clothoids*, JCAM 341 2018 | 10.1016/j.cam.2018.03.029 | Non-existence counterexamples as negative tests |
| | Meek & Walton, *Arc spline approximation to a clothoid*, JCAM 2004 | 10.1016/j.cam.2003.12.038 (aggregator) | O(1/n²) named approximation (not a chord lie) |

## CRV-NURBS
| | Paper | DOI | Targeted use |
|---|---|---|---|
| ★ | Piegl & Tiller, *The NURBS Book*, 2nd ed. 1997 | 10.1007/978-3-642-59223-2 | A2.1/A2.2 + knot-vector validity → WKB 21 validity predicates |
| | Chen, Ma, Xu, Paul, *Hausdorff distance between two B-spline curves*, CAD 42(12) 2010 | 10.1016/j.cad.2010.06.009 | NURBS Hausdorff oracle |
| | (+ Mainar & Peña 1999 above, covers de Boor) | | |

## GEO-TIN / PRF-TIN15
| | Paper | DOI | Targeted use |
|---|---|---|---|
| ★ | Ledoux, *Validation of solids per ISO geographic standards*, CACAIE 28(9) 2013 | 10.1111/mice.12043 | Ring→polygon→shell→solid validity with error codes |
| | Ledoux, *val3dity*, OGDSS 3:1 2018 | 10.1186/s40965-018-0043-x (OA) | Error catalogue + GPLv3 test geometries as differential oracle |
| | Biljecki et al., *Most common errors in CityGML*, ISPRS Annals IV-2/W1 2016 | 10.5194/isprs-annals-IV-2-W1-13-2016 (OA) | Real-world error frequencies → prioritisation |
| | Devillers & Teillaud, *Perturbations for (weighted) Delaunay 3D*, CGTA 44(3) 2011 | 10.1016/j.comgeo.2010.09.010 · HAL inria-00560388 | Symbolic perturbation; also TRI-VOR3 |

## H-ALPHA / TRI-VOR3 (HOLD)
| | Paper | DOI | Targeted use |
|---|---|---|---|
| | Edelsbrunner, Kirkpatrick, Seidel, *On the shape of a set of points*, IEEE TIT 29(4) 1983 | 10.1109/TIT.1983.1056714 | α-shape ⊆ Delaunay (planar seminal; card's anchor is the 3-D paper) |
| | Edelsbrunner, *Union of balls and its dual shape*, DCG 13 1995 | 10.1007/BF02574053 | Weighted α-complex for discs/balls — bridges H-ALPHA and H-IMPRECISE |
| | Edelsbrunner & Mücke, *Simulation of simplicity*, ACM TOG 9(1) 1990 | 10.1145/77635.77639 | Degenerate insphere handling |

## MMF-IO — standards (not peer-reviewed)
- ISO/IEC 13249-3:2016 SQL/MM Spatial — normative curve/surface types and WKB/WKT codes.
- ISO 19107:2019 Spatial schema — curve interpolations; val3dity conformance basis.
- OGC 06-103r4 SFA 1.2.1 / ISO 19125-1:2004.
- Esri `esriSegmentType` (1 arc, 4 cubic Bézier, 5 elliptic arc) — vendor spec; byte layout unconfirmed, cross-check GDAL `ogr/ogrpgeogeometry.cpp`.

---

## Suggested first hunts (shortest path to an outside user)
1. **H-IMPRECISE × Alt–Scharf**: one doc covering disc h_max (Knauer Thm 3) and arc–arc Hausdorff candidates; authors of both are reachable.
2. **CRV-TOUCH × Devillers et al. 2002**: their circle-arc predicate cases against the merged kiss spec.
3. **PRF-P7 × Kettner et al. classroom examples**: published failure inputs replayed through GEOS/NTS/oracle — easy, citable, postable.
