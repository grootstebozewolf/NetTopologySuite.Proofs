-- klic-demo stock run on PostGIS. Same predicates as stock_shapely.py.
-- Expects table pairs(dig text, cable text) and caseb(dig text, cable text).
-- BSD-3-Clause, NetTopologySuite.Proofs contributors.
\pset tuples_only on
\pset format unaligned
SELECT json_build_object(
  'tool', 'PostGIS',
  'version', 'PostGIS ' || postgis_lib_version() || ' / GEOS ' || postgis_geos_version(),
  'runtime', split_part(version(), ',', 1),
  'caseA', (SELECT json_build_object(
              'pairs', count(*),
              'nonempty', count(*) FILTER (WHERE NOT ST_IsEmpty(i)),
              'covers_false', count(*) FILTER (WHERE NOT ST_Covers(d, i)))
            FROM (SELECT ST_GeomFromText(dig) d,
                         ST_Intersection(ST_GeomFromText(cable), ST_GeomFromText(dig)) i
                  FROM pairs) q),
  'caseB', (SELECT json_build_object(
              'intersects', ST_Intersects(c, d),
              'relate', ST_Relate(d, c),
              'covers', ST_Covers(d, ST_Intersection(c, d)),
              'intersection', ST_AsText(ST_Intersection(c, d), 17))
            FROM (SELECT ST_GeomFromText(dig) d, ST_GeomFromText(cable) c FROM caseb) q)
);
