#!/usr/bin/env bash
# Run the Paragon test corpus and check it against the recorded baselines.
#
#   good/  a .para file is expected to typecheck (parac exits 0)
#   bad/   a .para file is expected to be REJECTED, and — crucially — rejected
#          for the right reason: each test ships a .exp file holding the error
#          message it is supposed to produce. Checking only the exit code
#          overstates the pass rate, because a test can be rejected by an
#          unrelated failure (e.g. an unimplemented statement form) and still
#          look green.
#
# Exits non-zero if either corpus falls below its baseline.

set -uo pipefail

cd "$(dirname "$0")/.."
SUITE=simpletestsuite

# Baselines. Raise these when the underlying gaps are fixed.
#   good: the remaining failures are statement forms tcStmt has no case for
#         (labeled break, switch), so they die on its catch-all before the
#         return-reachability analysis ever runs. checkReturnStmts already
#         handles those forms; the gap is in the typechecker, not in it.
#   bad:  3 of the 4 non-matching tests hit that same gap and so are vacuous;
#         1 (arrays/BasicArrayPolicies) reaches the right verdict but prints an
#         unsimplified policy expression.
GOOD_MIN=${GOOD_MIN:-109}
BAD_MIN=${BAD_MIN:-74}

PARAC=${PARAC:-$(find dist-newstyle -type f -name parac -perm -u+x 2>/dev/null | head -1)}
if [ -z "$PARAC" ] || [ ! -x "$PARAC" ]; then
  echo "error: parac not found; run 'cabal build all' first (or set PARAC=)" >&2
  exit 2
fi
PARAC=$(realpath "$PARAC")
LIB=$(realpath lib)

# parac writes .java/.pi next to its input; keep the tree clean on exit.
# Sweep both: a good/ test that starts passing emits a .pi that was not there
# before, and dropping only .java left those behind as untracked litter.
cleanup() {
  git ls-files --others --exclude-standard -- "$SUITE" \
    | grep -E '\.(java|pi)$' | xargs -r rm -f
  git checkout -- "$SUITE" 2>/dev/null || true
}
trap cleanup EXIT

good_pass=0 good_fail=0
while IFS= read -r f; do
  if (cd "$(dirname "$f")" && "$PARAC" -p "$LIB" "$(basename "$f")" >/dev/null 2>&1 </dev/null); then
    good_pass=$((good_pass + 1))
  else
    good_fail=$((good_fail + 1))
  fi
done < <(find "$SUITE/good" -name '*.para' | sort)

bad_match=0 bad_wrong=0 bad_accepted=0
mismatches=()
while IFS= read -r f; do
  out=$( (cd "$(dirname "$f")" && "$PARAC" -p "$LIB" "$(basename "$f")" 2>&1 </dev/null) )
  if [ $? -eq 0 ]; then
    bad_accepted=$((bad_accepted + 1))
    mismatches+=("$f  [ACCEPTED — should have been rejected]")
    continue
  fi
  exp="${f%.para}.exp"
  if [ ! -f "$exp" ]; then
    bad_wrong=$((bad_wrong + 1)); mismatches+=("$f  [no .exp oracle]"); continue
  fi
  # Every non-blank line of the .exp must appear somewhere in parac's output.
  ok=1
  while IFS= read -r line; do
    [ -z "${line// }" ] && continue
    grep -qF -- "$line" <<<"$out" || { ok=0; break; }
  done < "$exp"
  if [ "$ok" -eq 1 ]; then
    bad_match=$((bad_match + 1))
  else
    bad_wrong=$((bad_wrong + 1))
    mismatches+=("$f  [rejected, but not with its expected message]")
  fi
done < <(find "$SUITE/bad" -name '*.para' | sort)

good_total=$((good_pass + good_fail))
bad_total=$((bad_match + bad_wrong + bad_accepted))

echo
echo "good/  typechecked          : $good_pass / $good_total   (baseline >= $GOOD_MIN)"
echo "bad/   rejected as expected : $bad_match / $bad_total   (baseline >= $BAD_MIN)"
[ "$bad_accepted" -gt 0 ] && echo "bad/   WRONGLY ACCEPTED     : $bad_accepted"
echo

if [ ${#mismatches[@]} -gt 0 ]; then
  echo "bad/ tests not matching their oracle:"
  printf '  %s\n' "${mismatches[@]}"
  echo
fi

status=0
if [ "$good_pass" -lt "$GOOD_MIN" ]; then
  echo "FAIL: good/ regressed ($good_pass < $GOOD_MIN)"; status=1
fi
if [ "$bad_match" -lt "$BAD_MIN" ]; then
  echo "FAIL: bad/ regressed ($bad_match < $BAD_MIN)"; status=1
fi
if [ "$bad_accepted" -gt 0 ]; then
  echo "FAIL: $bad_accepted bad/ test(s) were accepted — a soundness regression"; status=1
fi
[ "$status" -eq 0 ] && echo "OK: at or above baseline."
exit $status
