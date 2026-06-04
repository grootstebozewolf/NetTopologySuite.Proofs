#!/usr/bin/env bash
# =============================================================================
# scripts/check_oracle_handrolled.sh
# -----------------------------------------------------------------------------
# Credibility ratchet for the oracle binary (oracle/driver.ml).
#
# The RocqRefRunner's value proposition is that every mode is bit-exact
# against a Coq-EXTRACTED reference (oracle/extracted.ml, generated from
# theories-flocq/Validate_binary64_extract.v).  Native float arithmetic
# hand-written in driver.ml -- code that merely *claims* to mirror an R-side
# Coq predicate with no machine-checked link -- undermines that guarantee.
#
# This is a RATCHET, not a ban: hand-rolled kernels are frozen in
# docs/oracle-handrolled-allowlist.txt, which defines two categories --
# TRANSITIONAL (tracked for migration, may only SHRINK) and INTERFACE-BOUNDARY
# (a sanctioned, permanent exception: a mode whose output is a TRANSCENDENTAL
# primitive the Java/JTS or C#/NTS implementation computes for differential
# testing, with no Coq-extractable form -- e.g. ARC_LENGTH's r*theta).  The
# script enforces "detected == allowlisted"; the category discipline (no new
# TRANSITIONAL kernels; new INTERFACE-BOUNDARY kernels only with a documented
# Java/C# justification) is a review rule recorded in the allowlist file.
#
#   - A function in driver.ml that does float arithmetic and is not on the
#     allowlist  -> FAILURE.  Hand-rolled numeric code must be allowlisted
#     (transitional debt, or a justified interface-boundary entry).
#   - An allowlist entry that no longer does float arithmetic in driver.ml
#     (migrated to an extracted call, or removed)  -> FAILURE, asking you to
#     prune the allowlist.
#
# "Does float arithmetic" = the function body (comments stripped) contains a
# binary64 operator (+. -. *. /.) or a float math / Float.* call.  Pure I/O
# helpers (parse_point via float_of_string, print_point via Printf "%h") and
# functions that only *call* extracted or already-allowlisted helpers do not
# trip the check.
#
# Exit codes:
#   0 -- detected hand-rolled set == allowlist (ratchet holds).
#   1 -- new hand-rolled function, or stale allowlist entry.
#   2 -- usage / file-access error.
# =============================================================================

set -u

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DRIVER="$REPO_ROOT/oracle/driver.ml"
ALLOWLIST="$REPO_ROOT/docs/oracle-handrolled-allowlist.txt"

for f in "$DRIVER" "$ALLOWLIST"; do
  if [ ! -r "$f" ]; then
    echo "[check_oracle_handrolled] cannot read $f" >&2
    exit 2
  fi
done

TMPDIR_RUN="$(mktemp -d)"
trap 'rm -rf "$TMPDIR_RUN"' EXIT
CODE="$TMPDIR_RUN/driver.code.ml"
DETECTED="$TMPDIR_RUN/detected.txt"
ALLOWED="$TMPDIR_RUN/allowed.txt"

# 1. Strip OCaml comments (nesting-aware) so arithmetic in doc comments is
#    not attributed to the preceding function.
perl -0777 -e '
  local $/; my $s=<>; my $out=""; my $d=0; my $i=0; my $n=length($s);
  while ($i<$n) {
    my $t=substr($s,$i,2);
    if ($t eq "(*") { $d++; $i+=2; next; }
    if ($t eq "*)" && $d>0) { $d--; $i+=2; next; }
    $out.=substr($s,$i,1) if $d==0;
    $i++;
  }
  print $out;
' "$DRIVER" > "$CODE"

# 2. Emit each top-level function whose (comment-free) body does float
#    arithmetic.  A function spans from its `let` at column 0 to the next.
#    Done in PERL, not awk, for cross-platform regex parity: the macOS CI
#    runner's BSD/one-true-awk diverges from gawk/mawk on regex char classes
#    ("/" inside [...]) and word boundaries (\< \>), and even mis-parses
#    function names -- perl behaves identically everywhere (and is already
#    used in step 1).  "Does float arithmetic" = a binary64 operator
#    (+. -. *. /.), a float math call as a whole word, or a Float.* call.
perl -ne '
  if (/^let\s+(?:rec\s+)?([A-Za-z_][A-Za-z0-9_]*)/) {
    print "$cur\n" if $cur && $hit;
    $cur = $1; $hit = 0;
  }
  $hit = 1 if m{[-+*/]\.};
  $hit = 1 if m{\b(?:acos|asin|atan2|atan|cos|sin|tan|sqrt|exp|log)\b};
  $hit = 1 if m{Float\.(?:min|max|abs|is_finite|is_nan)};
  END { print "$cur\n" if $cur && $hit; }
' "$CODE" | sort -u > "$DETECTED"

# 3. Allowlist: one function name per line; `#` comments and blanks ignored.
grep -vE '^[[:space:]]*(#|$)' "$ALLOWLIST" | awk '{print $1}' | sort -u > "$ALLOWED"

NEW="$(comm -23 "$DETECTED" "$ALLOWED")"
STALE="$(comm -13 "$DETECTED" "$ALLOWED")"

status=0

if [ -n "$NEW" ]; then
  status=1
  echo "::error::New hand-rolled float arithmetic in oracle/driver.ml is not allowed." >&2
  echo "The oracle reference must be Coq-EXTRACTED, not hand-mirrored.  These" >&2
  echo "functions do float arithmetic but are not on the ratchet allowlist:" >&2
  echo "$NEW" | sed 's/^/    /' >&2
  echo "" >&2
  echo "Route the mode through an extracted function (add it to the" >&2
  echo "Extraction call in theories-flocq/Validate_binary64_extract.v and" >&2
  echo "call it from driver.ml).  See docs/oracle-handroll-migration.md." >&2
fi

if [ -n "$STALE" ]; then
  status=1
  echo "::error::Stale entry in docs/oracle-handrolled-allowlist.txt." >&2
  echo "These allowlisted names no longer do hand-rolled arithmetic in" >&2
  echo "driver.ml (migrated to extracted, or renamed/removed).  The ratchet" >&2
  echo "only tightens -- remove them from the allowlist:" >&2
  echo "$STALE" | sed 's/^/    /' >&2
fi

if [ "$status" -eq 0 ]; then
  n=$(wc -l < "$ALLOWED" | tr -d ' ')
  echo "[check_oracle_handrolled] ratchet holds: $n frozen hand-rolled kernel(s), no new ones."
fi

exit "$status"
