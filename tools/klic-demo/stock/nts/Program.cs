// klic-demo stock run on NetTopologySuite. Same predicates as stock_shapely.py.
// Usage: dotnet run --project tools/klic-demo/stock/nts -- <caseA_pairs.wkt> <caseC.wkt> <klic_handover_mm.wkt>
// BSD-3-Clause, NetTopologySuite.Proofs contributors.
using System.Reflection;
using NetTopologySuite.Geometries;
using NetTopologySuite.IO;
using NetTopologySuite.Operation.Overlay;
using NetTopologySuite.Operation.OverlayNG;
using NetTopologySuite.Precision;

var reader = new WKTReader();
string J(bool v) => v ? "true" : "false";
string Js(IEnumerable<bool> v) => "[" + string.Join(",", v.Select(J)) + "]";

int n = 0, nonEmpty = 0, coversFalse = 0;
foreach (var line in File.ReadLines(args[0]))
{
    if (string.IsNullOrWhiteSpace(line)) continue;
    var f = line.Split(';');
    var d = reader.Read(f[0]); var c = reader.Read(f[1]);
    var inter = c.Intersection(d);
    n++;
    if (!inter.IsEmpty) nonEmpty++;
    if (!d.Covers(inter)) coversFalse++;
}
var cc = File.ReadLines(args[1]).First().Split(';');
var digC = reader.Read(cc[0]); var cableC = reader.Read(cc[1]);
var interC = cableC.Intersection(digC);

var h = new Dictionary<string, Geometry>();
foreach (var line in File.ReadLines(args[2]))
{
    if (line.StartsWith("#") || string.IsNullOrWhiteSpace(line)) continue;
    var f = line.Split('\t');
    h[f[0]] = reader.Read(f[3]);
}
var dig = h["GP-0001"]; var ls = h["LS-0042"]; var ms = h["MS-0007"];
var mm = new PrecisionModel(1.0);
var interA = ls.Intersection(dig);
var pts = interA.Coordinates.Select(p => dig.Factory.CreatePoint(p)).ToList();
var srA = OverlayNG.Overlay(ls, dig, SpatialFunction.Intersection, mm);
var srCovers = GeometryPrecisionReducer.Reduce(dig, mm).Covers(srA);
var srB = OverlayNG.Overlay(ms, dig, SpatialFunction.Intersection, mm);
var reduced = GeometryPrecisionReducer.Reduce(ms, mm).Intersects(GeometryPrecisionReducer.Reduce(dig, mm));

var ver = typeof(Geometry).Assembly.GetCustomAttribute<AssemblyInformationalVersionAttribute>()?.InformationalVersion
          ?? typeof(Geometry).Assembly.GetName().Version.ToString();
Console.WriteLine("{\"tool\":\"NTS\",\"version\":\"NetTopologySuite " + ver.Split('+')[0] + "\",\"runtime\":\".NET "
    + Environment.Version + "\",\"randomA\":{\"pairs\":" + n + ",\"nonempty\":" + nonEmpty + ",\"covers_false\":" + coversFalse
    + "},\"caseA\":{\"covers\":" + J(dig.Covers(interA)) + ",\"within\":" + J(interA.Within(dig))
    + ",\"points_on_cable\":" + Js(pts.Select(p => ls.Intersects(p))) + ",\"points_on_boundary\":" + Js(pts.Select(p => dig.Boundary.Intersects(p)))
    + ",\"sr_covers\":" + J(srCovers) + "},\"caseB\":{\"intersects\":" + J(ms.Intersects(dig))
    + ",\"intersection_empty\":" + J(ms.Intersection(dig).IsEmpty) + ",\"sr_intersection\":\"" + new WKTWriter().Write(srB)
    + "\",\"reduced_intersects\":" + J(reduced) + "},\"caseC\":{\"intersects\":" + J(cableC.Intersects(digC)) + ",\"relate\":\"" + digC.Relate(cableC)
    + "\",\"covers\":" + J(digC.Covers(interC)) + ",\"intersection\":\"" + new WKTWriter().Write(interC) + "\"}}");
