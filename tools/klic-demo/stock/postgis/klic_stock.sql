-- klic-demo stock run on PostGIS. Same predicates as stock_shapely.py.
-- Expects tables pairs(dig, cable), casec(dig, cable), handover(fid, typ, thema, wkt).
-- BSD-3-Clause, NetTopologySuite.Proofs contributors.
\pset tuples_only on
\pset format unaligned
WITH h AS (
  SELECT (SELECT ST_GeomFromText(wkt) FROM handover WHERE fid = 'GP-0001') AS dig,
         (SELECT ST_GeomFromText(wkt) FROM handover WHERE fid = 'LS-0042') AS ls,
         (SELECT ST_GeomFromText(wkt) FROM handover WHERE fid = 'MS-0007') AS ms
), a AS (
  SELECT dig, ls, ms, ST_Intersection(ls, dig) AS i, ST_Intersection(ls, dig, 1.0) AS sr FROM h
)
SELECT json_build_object(
  'tool', 'PostGIS',
  'version', 'PostGIS ' || postgis_lib_version() || ' / GEOS ' || postgis_geos_version(),
  'runtime', split_part(version(), ',', 1),
  'randomA', (SELECT json_build_object(
              'pairs', count(*),
              'nonempty', count(*) FILTER (WHERE NOT ST_IsEmpty(i)),
              'covers_false', count(*) FILTER (WHERE NOT ST_Covers(d, i)))
            FROM (SELECT ST_GeomFromText(dig) d,
                         ST_Intersection(ST_GeomFromText(cable), ST_GeomFromText(dig)) i
                  FROM pairs) q),
  'caseA', (SELECT json_build_object(
              'covers', ST_Covers(dig, i),
              'within', ST_Within(i, dig),
              'points_on_cable', (SELECT json_agg(ST_Intersects(ls, (dp).geom) ORDER BY (dp).path) FROM ST_DumpPoints(i) dp),
              'points_on_boundary', (SELECT json_agg(ST_Intersects(ST_Boundary(dig), (dp).geom) ORDER BY (dp).path) FROM ST_DumpPoints(i) dp),
              'sr_covers', ST_Covers(ST_ReducePrecision(dig, 1.0), sr)) FROM a),
  'caseB', (SELECT json_build_object(
              'intersects', ST_Intersects(ms, dig),
              'intersection_empty', ST_IsEmpty(ST_Intersection(ms, dig)),
              'sr_intersection', ST_AsText(ST_Intersection(ms, dig, 1.0)),
              'reduced_intersects', ST_Intersects(ST_ReducePrecision(ms, 1.0), ST_ReducePrecision(dig, 1.0))) FROM h),
  'caseC', (SELECT json_build_object(
              'intersects', ST_Intersects(c, d),
              'relate', ST_Relate(d, c),
              'covers', ST_Covers(d, ST_Intersection(c, d)),
              'intersection', ST_AsText(ST_Intersection(c, d), 17))
            FROM (SELECT ST_GeomFromText(dig) d, ST_GeomFromText(cable) c FROM casec) q)
);
