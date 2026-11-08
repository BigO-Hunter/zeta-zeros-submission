#!/usr/bin/env bash
# route_watch.sh — critical-line-zeros route-opener watcher.
#
# Checks the two signals the maintainer named:
#   (1) board announcements: board.bigospeedrun.com posts feed
#   (2) challenges/ additions in bigospeedrun/verifier (GitHub contents API)
# plus statement drift on Challenge.lean (any change = re-run the readiness audit).
#
# TRIGGER lines mean: the route may be opening — read the post/dir and run the filing
# checklist at the bottom of Submission/ReadyRaceBound.lean. No TRIGGER = still WAITING.
# State (Challenge.lean hash) is kept next to this script in .route_watch_state.
# Exit code: 0 = waiting, 1 = TRIGGER fired.
set -u
DIR="$(cd "$(dirname "$0")" && pwd)"
BOARD_URL="https://board.bigospeedrun.com/api/posts?board=other-critical-line-zeros&format=md"
CHAL_API="https://api.github.com/repos/bigospeedrun/verifier/contents/challenges"
CHAL_DIR="https://api.github.com/repos/bigospeedrun/verifier/contents/challenges/critical-line-zeros"
CHAL_RAW="https://raw.githubusercontent.com/bigospeedrun/verifier/main/challenges/critical-line-zeros/Challenge.lean"
STAMP="$DIR/../.route_watch_state"
TRIG=0
echo "== $(date -u +%FT%TZ) critical-line-zeros route check =="

echo "-- (1) board feed: other-critical-line-zeros --"
BOARD="$(curl -fsSL --max-time 20 "$BOARD_URL" 2>/dev/null || true)"
if [ -z "$BOARD" ]; then
  echo "  (board feed unreachable or empty)"
else
  echo "$BOARD" | head -c 1500; echo
  if echo "$BOARD" | grep -iq -e 'open for submission' -e 'now open' -e 'route opens' -e 'accepting submission'; then
    echo "TRIGGER(board): announcement language found — READ THE POST ABOVE"
    TRIG=1
  fi
fi

echo "-- (2) verifier challenges/ directory --"
CHAL="$(curl -fsSL --max-time 20 "$CHAL_API" 2>/dev/null || true)"
if [ -z "$CHAL" ]; then
  echo "  (github api unreachable)"
else
  echo "$CHAL" | grep -o '"name": *"[^"]*"' | sed 's/"name": */  /'
  if echo "$CHAL" | grep -q 'critical-line-zeros'; then
    echo "  critical-line-zeros dir present; contents:"
    DIRLIST="$(curl -fsSL --max-time 20 "$CHAL_DIR" 2>/dev/null || true)"
    echo "$DIRLIST" | grep -o '"name": *"[^"]*"' | sed 's/"name": */    /'
    if echo "$DIRLIST" | grep -q '"name"'; then
      echo "$DIRLIST" | grep -o '"name": *"[^"]*"' | sed 's/"name": */    /'
      # Known CLOSED-profile baseline; anything NEW in the dir is a route signal.
      EXTRA="$(echo "$DIRLIST" | grep -o '"name": *"[^"]*"' \
        | grep -v -e '"Challenge.lean"' -e '"LICENSE"' -e '"NOTICE"' -e '"README.md"' -e '"provenance.json"' || true)"
      if [ -n "$EXTRA" ]; then
        echo "TRIGGER(dir): NEW file(s) in the challenge dir beyond the closed-profile baseline:"
        echo "$EXTRA"
        TRIG=1
      fi
    fi
  else
    echo "  critical-line-zeros dir ABSENT (not yet a public challenge)"
  fi
fi

echo "-- (3) Challenge.lean statement drift --"
CUR="$(curl -fsSL --max-time 20 "$CHAL_RAW" 2>/dev/null | shasum -a 256 | cut -d' ' -f1 || true)"
if [ -z "$CUR" ]; then
  echo "  (challenge file unreachable)"
else
  OLD="$(cat "$STAMP" 2>/dev/null || true)"
  echo "  sha256: $CUR"
  if [ -n "$OLD" ] && [ "$OLD" != "$CUR" ]; then
    echo "TRIGGER(drift): Challenge.lean CHANGED since last run — RE-AUDIT statements"
    TRIG=1
  fi
  echo "$CUR" > "$STAMP"
fi

if [ "$TRIG" = 1 ]; then
  echo "== VERDICT: TRIGGER — run the filing checklist (Submission/ReadyRaceBound.lean bottom) =="
  exit 1
fi
echo "== VERDICT: no trigger — still WAITING (package staged and green) =="
exit 0
