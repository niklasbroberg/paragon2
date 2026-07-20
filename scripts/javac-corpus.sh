#!/usr/bin/env bash
#
# Baseline harness for issue #1 (Java codegen targets the superseded v1 runtime).
#
# Runs parac over simpletestsuite/good/, then tries to javac each generated
# .java against the v2 runtime in lib/se/chalmers/paragon/runtime/, and reports
# how many compile. That number is the feedback signal the Compile.hs retarget
# currently lacks: today's codegen emits the v1 flat API (Lock.newLock,
# Policy.newPClause, Actor.newActorVariable, ...) which does not exist in v2, so
# the expected starting point is ~0. Retarget incrementally and watch it climb.
#
# IMPORTANT: a rising count means the emitted Java *compiles*, NOT that it
# enforces policies correctly. There is no oracle for v2 output (Bart's 2014
# tarball is authoritative for v1; the 101/102 .pi identity comes from
# PiGeneration, not Compile). Treat this as necessary-not-sufficient.
#
# Usage:
#   scripts/javac-corpus.sh              # summary
#   scripts/javac-corpus.sh -v           # + first error per failing file
#   scripts/javac-corpus.sh --errors     # + histogram of missing v1 symbols

set -uo pipefail
cd "$(dirname "$0")/.."
REPO="$PWD"

VERBOSE=0; ERRORS=0
for a in "$@"; do
  case "$a" in
    -v|--verbose) VERBOSE=1 ;;
    --errors)     ERRORS=1 ;;
    *) echo "unknown option: $a" >&2; exit 2 ;;
  esac
done

PARAC=${PARAC:-$(find dist-newstyle -type f -name parac -perm -u+x 2>/dev/null | head -1)}
[ -n "$PARAC" ] && [ -x "$PARAC" ] || { echo "error: parac not found; cabal build all" >&2; exit 2; }
PARAC=$(realpath "$PARAC")   # loop cd's into test dirs; relative path would break
LIB="$REPO/lib"
RUNTIME_SRC="$LIB/se/chalmers/paragon/runtime"

command -v javac >/dev/null || { echo "error: javac not found" >&2; exit 2; }

WORK=$(mktemp -d)
RTC="$WORK/runtime-classes"; mkdir -p "$RTC"
STAGE="$WORK/stage";         mkdir -p "$STAGE"
OUT="$WORK/out";             mkdir -p "$OUT"

# --- 1. build the v2 runtime we are compiling against -----------------------
echo "building v2 runtime ($RUNTIME_SRC)..."
if ! javac -nowarn -d "$RTC" $(find "$RUNTIME_SRC" -name '*.java') 2>"$WORK/rt.err"; then
  echo "error: the v2 runtime itself does not compile:" >&2
  head -20 "$WORK/rt.err" >&2
  exit 1
fi
echo "v2 runtime OK"

# --- 2. generate .java from the corpus --------------------------------------
# parac writes .java/.pi next to its input. Two kinds of litter to undo after:
# new untracked files, and OVERWRITTEN tracked references (good/codegen/
# UseNative.pi is rewritten every run -- issue #5). Restore both.
snap_untracked() { git status --porcelain -uall | awk '/^\?\?/{print $2}' | sort; }
snap_modified()  { git status --porcelain -uall | awk '/^ ?M/{print $2}' | sort; }
before_u=$(snap_untracked); before_m=$(snap_modified)
cleanup() {
  comm -13 <(printf '%s\n' "$before_u") <(snap_untracked) \
    | grep -E '\.(java|pi)$' | while read -r f; do rm -f "$f"; done
  comm -13 <(printf '%s\n' "$before_m") <(snap_modified) \
    | grep -E '^simpletestsuite/.*\.pi$' | while read -r f; do git checkout -- "$f"; done
  rm -rf "$WORK"
}
trap cleanup EXIT

gen=0; nogen=0
while read -r f; do
  d=$(dirname "$f"); b=$(basename "$f" .para)
  (cd "$d" && "$PARAC" -p "$LIB" "$b.para" >/dev/null 2>&1 </dev/null)
  if [ -f "$d/$b.java" ]; then
    rel=${d#simpletestsuite/good/}
    mkdir -p "$STAGE/$rel"
    cp "$d/$b.java" "$STAGE/$rel/"
    gen=$((gen+1))
  else
    nogen=$((nogen+1))
  fi
done < <(find simpletestsuite/good -name '*.para' | sort)

# --- 3. javac each generated file against the v2 runtime --------------------
ok=0; bad=0
: > "$WORK/fail.txt"; : > "$WORK/sym.txt"
while read -r j; do
  if javac -nowarn -cp "$RTC" -d "$OUT" "$j" 2>"$WORK/e.txt"; then
    ok=$((ok+1))
  else
    bad=$((bad+1))
    { echo "--- ${j#$STAGE/}"; head -3 "$WORK/e.txt"; } >> "$WORK/fail.txt"
    # Classify PER ERROR, not per file -- a file can have both problems, and
    # they are independent (see issue #5). javac reports the missing v1 package
    # AND the lowering errors in the same run, so a first-match-wins classifier
    # silently hides every lowering gap behind the package error: that bug made
    # this script report 2 lowering failures where issue #5 documents 11.
    if grep -q "package se\.chalmers\.paragon does not exist" "$WORK/e.txt"; then
      echo "$j" >> "$WORK/v1.txt"
      grep -oE "paragon\.(Lock|Policy|Actor|Atom|ActorList|Util)\.[a-zA-Z]+" "$j" \
        | sed 's/^paragon\.//' >> "$WORK/sym.txt"
    fi
    # Residual = errors that are NOT the missing v1 package. These are the
    # Paragon/Java lowering gaps (issue #5) and survive the #1 retarget.
    grep "error:" "$WORK/e.txt" \
      | grep -v "package se\.chalmers\.paragon does not exist" > "$WORK/resid.txt"
    if [ -s "$WORK/resid.txt" ]; then
      echo "$j" >> "$WORK/other.txt"
      sed -E 's/^.*error: //; s/\b[A-Za-z_][A-Za-z0-9_]*\b$/<name>/' "$WORK/resid.txt" \
        | sort -u >> "$WORK/othersym.txt"
    fi
  fi
done < <(find "$STAGE" -name '*.java' | sort)

# --- 4. report ---------------------------------------------------------------
total=$((ok+bad))
echo
echo "=== javac against v2 runtime (lib/se/chalmers/paragon/runtime)"
echo ".para files          : $((gen+nogen))"
echo "  generated .java    : $gen"
echo "  no .java (rejected): $nogen"
echo "javac compiled       : $ok / $total"
echo "javac failed         : $bad / $total"
v1=$( [ -f "$WORK/v1.txt" ] && wc -l < "$WORK/v1.txt" || echo 0 )
other=$( [ -f "$WORK/other.txt" ] && wc -l < "$WORK/other.txt" || echo 0 )
echo "  hit missing v1 API : $v1   <-- issue #1 (the retarget target)"
echo "  hit lowering gaps  : $other   <-- issue #5 (SURVIVES the retarget)"
echo
echo "NOTE: the two categories OVERLAP -- a file can have both, and javac reports"
echo "  both in one run. Most generated .java never touches the runtime at all,"
echo "  so the headline $ok/$total overstates progress; and fixing #1 will NOT take"
echo "  the failures to zero, because the $other lowering-gap files stay broken."

if [ "$ERRORS" = 1 ] && [ -s "$WORK/sym.txt" ]; then
  echo
  echo "--- v1 entry points emitted (retarget checklist, by frequency) ---"
  sort "$WORK/sym.txt" | uniq -c | sort -rn | head -20
fi
if [ "$ERRORS" = 1 ] && [ -s "$WORK/other.txt" ]; then
  echo
  echo "--- lowering-gap files (issue #5; independent of the runtime API) ---"
  sed "s|^$STAGE/||" "$WORK/other.txt"
  if [ -s "$WORK/othersym.txt" ]; then
    echo "--- their error kinds ---"
    sort -u "$WORK/othersym.txt" | head -12
  fi
fi
if [ "$VERBOSE" = 1 ] && [ -s "$WORK/fail.txt" ]; then
  echo
  echo "--- first error per failing file (head) ---"
  head -60 "$WORK/fail.txt"
fi

# Deliberately exits 0 regardless: this is a BASELINE meter, not a pass/fail
# gate. Wiring it into CI as a gate would freeze in whatever number is current.
exit 0
