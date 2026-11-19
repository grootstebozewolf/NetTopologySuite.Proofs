"""(From the first-build handover, kept verbatim apart from output file names.
Run from tools/klic-demo.)
Generate the SYNTHETIC, KLIC-shaped demo dataset (run once; output is committed).
Not a real KLIC delivery. IMKL-like attributes, RD New (EPSG:28992).
Canonical coordinates are float64 millimetres (RD New x/y * 1000), so the
1 mm KLIC precision grid is the unit grid the Rocq theorems are stated on."""
import json, random, math
from shapely.geometry import Polygon, LineString
random.seed(7); f = random.random
X0, Y0 = 155_000_000.0, 463_000_000.0          # RD New origin area (Amersfoort), in mm
dig = Polygon([(X0+1203.37+f(), Y0+512.81+f()), (X0+12950.62+f(), Y0+240.17+f()),
               (X0+14210.44+f(), Y0+8230.09+f()), (X0+6120.55+f(), Y0+10480.73+f()),
               (X0+410.92+f(), Y0+7710.36+f())])
random.seed(1)
c1 = LineString([(X0-3000+1000*f()+f(), Y0+3000+4000*f()+f()), (X0+18000+f(), Y0+2000+6000*f()+f())])
# c2: passes 0.3 mm outside dig vertex 2, nearly tangent (a near-miss at a hot pixel)
vx, vy = dig.exterior.coords[2]
cx, cy = dig.centroid.x, dig.centroid.y
ux, uy = vx-cx, vy-cy; n = math.hypot(ux, uy); ux, uy = ux/n, uy/n
qx, qy = vx+0.3*ux, vy+0.3*uy                   # 0.3 mm outward from the vertex
tx, ty = -uy, ux                                # tangent direction
c2 = LineString([(qx-9000*tx, qy-9000*ty), (qx+6000*tx, qy+6000*ty)])
feats = [("graafpolygoon", "GP-0001", "Graafpolygoon", None, dig),
         ("kabel", "LS-0042", "Elektriciteitskabel", "laagspanning", c1),
         ("kabel", "MS-0007", "Elektriciteitskabel", "middenspanning", c2)]
with open("data/klic_handover_mm.wkt", "w") as fh:
    fh.write("# SYNTHETIC, KLIC-shaped (IMKL structure, RD New EPSG:28992), coordinates in MILLIMETRES (x1000).\n")
    fh.write("# Canonical input for both sides of the demo. Python repr floats round-trip exactly.\n")
    for kind, fid, typ, thema, g in feats:
        coords = ", ".join(f"{x!r} {y!r}" for x, y in g.exterior.coords) if kind == "graafpolygoon" else ", ".join(f"{x!r} {y!r}" for x, y in g.coords)
        wkt = f"POLYGON (({coords}))" if kind == "graafpolygoon" else f"LINESTRING ({coords})"
        fh.write(f"{fid}\t{typ}\t{thema or ''}\t{wkt}\n")
def to_m(cs): return [[x/1000.0, y/1000.0] for x, y in cs]
fc = {"type": "FeatureCollection", "name": "klic_synthetic",
      "crs": {"type": "name", "properties": {"name": "urn:ogc:def:crs:EPSG::28992"}},
      "provenance": "SYNTHETIC, KLIC-shaped (IMKL structure, RD New EPSG:28992). Display copy in metres; canonical input is data/klic_handover_mm.wkt.",
      "features": []}
for kind, fid, typ, thema, g in feats:
    geom = {"type": "Polygon", "coordinates": [to_m(g.exterior.coords)]} if kind == "graafpolygoon" else {"type": "LineString", "coordinates": to_m(g.coords)}
    props = {"imklType": typ, "identificatie": fid, "synthetic": True}
    if thema: props["thema"] = thema
    fc["features"].append({"type": "Feature", "properties": props, "geometry": geom})
json.dump(fc, open("data/klic_handover.geojson", "w"), indent=1)
print("wrote data/klic_handover_mm.wkt, data/klic_handover.geojson")
