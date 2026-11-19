// klic-demo stock run on JTS (jts-core). Same predicates as stock_shapely.py.
// Usage: java -cp lib/jts-core-<v>.jar KlicStock.java <caseA_pairs.wkt> <caseC.wkt> <klic_handover_mm.wkt>
// Prints one JSON object.  BSD-3-Clause, NetTopologySuite.Proofs contributors.
import java.nio.file.*;
import java.util.*;
import org.locationtech.jts.geom.*;
import org.locationtech.jts.io.WKTReader;
import org.locationtech.jts.io.WKTWriter;
import org.locationtech.jts.operation.overlayng.OverlayNG;
import org.locationtech.jts.precision.GeometryPrecisionReducer;

public class KlicStock {
  static String bools(List<Boolean> v) {
    StringBuilder b = new StringBuilder("[");
    for (int i = 0; i < v.size(); i++) b.append(i > 0 ? "," : "").append(v.get(i));
    return b.append("]").toString();
  }

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
    String[] c = Files.readAllLines(Paths.get(a[1])).get(0).split(";");
    Geometry digC = r.read(c[0]), cableC = r.read(c[1]);
    Geometry interC = cableC.intersection(digC);

    Map<String, Geometry> h = new HashMap<>();
    for (String line : Files.readAllLines(Paths.get(a[2]))) {
      if (line.startsWith("#") || line.isBlank()) continue;
      String[] f = line.split("\t");
      h.put(f[0], r.read(f[3]));
    }
    Geometry dig = h.get("GP-0001"), ls = h.get("LS-0042"), ms = h.get("MS-0007");
    PrecisionModel mm = new PrecisionModel(1.0);
    GeometryFactory gf = dig.getFactory();
    Geometry interA = ls.intersection(dig);
    List<Boolean> onCable = new ArrayList<>(), onBoundary = new ArrayList<>();
    for (Coordinate p : interA.getCoordinates()) {
      Point pt = gf.createPoint(p);
      onCable.add(ls.intersects(pt));
      onBoundary.add(dig.getBoundary().intersects(pt));
    }
    Geometry srA = OverlayNG.overlay(ls, dig, OverlayNG.INTERSECTION, mm);
    boolean srCovers = GeometryPrecisionReducer.reduce(dig, mm).covers(srA);
    Geometry srB = OverlayNG.overlay(ms, dig, OverlayNG.INTERSECTION, mm);
    boolean reduced = GeometryPrecisionReducer.reduce(ms, mm).intersects(GeometryPrecisionReducer.reduce(dig, mm));

    String ver = org.locationtech.jts.JTSVersion.CURRENT_VERSION.toString();
    System.out.println("{\"tool\":\"JTS\",\"version\":\"jts-core " + ver + "\",\"runtime\":\"Java "
        + System.getProperty("java.version") + "\","
        + "\"randomA\":{\"pairs\":" + n + ",\"nonempty\":" + nonEmpty + ",\"covers_false\":" + coversFalse + "},"
        + "\"caseA\":{\"covers\":" + dig.covers(interA) + ",\"within\":" + interA.within(dig)
        + ",\"points_on_cable\":" + bools(onCable) + ",\"points_on_boundary\":" + bools(onBoundary)
        + ",\"sr_covers\":" + srCovers + "},"
        + "\"caseB\":{\"intersects\":" + ms.intersects(dig) + ",\"intersection_empty\":" + ms.intersection(dig).isEmpty()
        + ",\"sr_intersection\":\"" + new WKTWriter().write(srB) + "\",\"reduced_intersects\":" + reduced + "},"
        + "\"caseC\":{\"intersects\":" + cableC.intersects(digC) + ",\"relate\":\"" + digC.relate(cableC).toString()
        + "\",\"covers\":" + digC.covers(interC) + ",\"intersection\":\"" + interC.toText() + "\"}}");
  }
}
