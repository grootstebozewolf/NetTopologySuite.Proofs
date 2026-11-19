// klic-demo stock run on NetTopologySuite. Same predicates as stock_shapely.py.
// Usage: dotnet run --project tools/klic-demo/stock/nts -- <caseA_pairs.wkt> <caseB.wkt>
// BSD-3-Clause, NetTopologySuite.Proofs contributors.
using System.Reflection;
using NetTopologySuite.Geometries;
using NetTopologySuite.IO;

var reader = new WKTReader();
int n = 0, nonEmpty = 0, coversFalse = 0;
foreach (var line in File.ReadLines(args[0]))
{
    if (string.IsNullOrWhiteSpace(line)) continue;
    var f = line.Split(';');
    var dig = reader.Read(f[0]); var cable = reader.Read(f[1]);
    var inter = cable.Intersection(dig);
    n++;
    if (!inter.IsEmpty) nonEmpty++;
    if (!dig.Covers(inter)) coversFalse++;
}
var b = File.ReadLines(args[1]).First().Split(';');
var digB = reader.Read(b[0]); var cableB = reader.Read(b[1]);
var interB = cableB.Intersection(digB);
var ver = typeof(Geometry).Assembly.GetCustomAttribute<AssemblyInformationalVersionAttribute>()?.InformationalVersion
          ?? typeof(Geometry).Assembly.GetName().Version.ToString();
string J(bool v) => v ? "true" : "false";
Console.WriteLine("{\"tool\":\"NTS\",\"version\":\"NetTopologySuite " + ver.Split('+')[0] + "\",\"runtime\":\".NET "
    + Environment.Version + "\",\"caseA\":{\"pairs\":" + n + ",\"nonempty\":" + nonEmpty + ",\"covers_false\":" + coversFalse
    + "},\"caseB\":{\"intersects\":" + J(cableB.Intersects(digB)) + ",\"relate\":\"" + digB.Relate(cableB)
    + "\",\"covers\":" + J(digB.Covers(interB)) + ",\"intersection\":\"" + new WKTWriter().Write(interB) + "\"}}");
