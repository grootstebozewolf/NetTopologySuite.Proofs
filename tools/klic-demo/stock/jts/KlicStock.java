// klic-demo stock run on JTS (jts-core). Same predicates as stock_shapely.py.
// Usage: java -cp lib/jts-core-<v>.jar KlicStock.java <caseA_pairs.wkt> <caseB.wkt>
// Prints one JSON object.  BSD-3-Clause, NetTopologySuite.Proofs contributors.
import java.nio.file.*;
import java.util.*;
import org.locationtech.jts.geom.*;
import org.locationtech.jts.io.WKTReader;

public class KlicStock {
  public static void main(String[] a) throws Exception {
    WKTReader r = new WKTReader();
    int n = 0, nonEmpty = 0, coversFalse = 0;
    for (String line : Files.readAllLines(Paths.get(a[0]))) {
      if (line.isBlank()) continue;
      String[] f = line.split(";");
      Geometry dig = r.read(f[0]), cable = r.read(f[1]);
      Geometry inter = cable.intersection(dig);
      n++;
      if (!inter.isEmpty()) nonEmpty++;
      if (!dig.covers(inter)) coversFalse++;
    }
    String[] b = Files.readAllLines(Paths.get(a[1])).get(0).split(";");
    Geometry dig = r.read(b[0]), cable = r.read(b[1]);
    Geometry inter = cable.intersection(dig);
    String ver = org.locationtech.jts.JTSVersion.CURRENT_VERSION.toString();
    System.out.println("{\"tool\":\"JTS\",\"version\":\"jts-core " + ver + "\",\"runtime\":\"Java "
        + System.getProperty("java.version") + "\","
        + "\"caseA\":{\"pairs\":" + n + ",\"nonempty\":" + nonEmpty + ",\"covers_false\":" + coversFalse + "},"
        + "\"caseB\":{\"intersects\":" + cable.intersects(dig) + ",\"relate\":\"" + dig.relate(cable).toString()
        + "\",\"covers\":" + dig.covers(inter) + ",\"intersection\":\"" + inter.toText() + "\"}}");
  }
}
