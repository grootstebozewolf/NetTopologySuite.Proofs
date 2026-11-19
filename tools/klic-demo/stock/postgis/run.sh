#!/usr/bin/env bash
# Run the klic-demo stock predicates in a throwaway PostGIS container.
# Usage: stock/postgis/run.sh <caseA_pairs.wkt> <caseC.wkt> <klic_handover_mm.wkt>   (prints one JSON line)
set -euo pipefail
IMAGE="${POSTGIS_IMAGE:-postgis/postgis:17-3.5}"
here="$(cd "$(dirname "$0")" && pwd)"
a="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
b="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
h="$(cd "$(dirname "$3")" && pwd)/$(basename "$3")"
name="klic-demo-postgis-$$"
docker run -d --rm --name "$name" -e POSTGRES_PASSWORD=klic \
  -v "$a:/in/a.wkt:ro" -v "$b:/in/b.wkt:ro" -v "$h:/in/h.wkt:ro" -v "$here/klic_stock.sql:/in/q.sql:ro" \
  "$IMAGE" >/dev/null
trap 'docker rm -f "$name" >/dev/null 2>&1 || true' EXIT
for _ in $(seq 1 60); do
  docker exec "$name" pg_isready -U postgres -h 127.0.0.1 >/dev/null 2>&1 && break; sleep 1
done
sleep 2
psql_() { docker exec -i "$name" psql -v ON_ERROR_STOP=1 -q -U postgres -h 127.0.0.1 "$@"; }
psql_ -c "CREATE EXTENSION IF NOT EXISTS postgis;" >/dev/null 2>&1
psql_ -c "CREATE TABLE pairs(dig text, cable text); CREATE TABLE casec(dig text, cable text); CREATE TABLE handover(fid text, typ text, thema text, wkt text);" >/dev/null
psql_ -c "\copy pairs FROM '/in/a.wkt' WITH (FORMAT text, DELIMITER ';')" >/dev/null
psql_ -c "\copy casec FROM '/in/b.wkt' WITH (FORMAT text, DELIMITER ';')" >/dev/null
docker exec "$name" bash -c "grep -v '^#' /in/h.wkt > /tmp/h.tsv"
psql_ -c "\copy handover FROM '/tmp/h.tsv' WITH (FORMAT text, DELIMITER E'\t')" >/dev/null
psql_ -f /in/q.sql
