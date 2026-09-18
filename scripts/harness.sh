#!/usr/bin/env bash
# Harness: build + sorry count + axiom check -> HARNESS_LOG.md
# Run from repo root: bash scripts/harness.sh
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

LOG=HARNESS_LOG.md
{
  echo "# Harness log"
  echo
  echo "- date: $(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  echo "- sha: $(git rev-parse HEAD 2>/dev/null || echo none)"
  echo "- toolchain: $(cat lean-toolchain)"
  echo

  echo "## lake build"
  echo '```'
  lake build 2>&1
  BUILD=$?
  echo "exit=$BUILD"
  echo '```'
  echo

  echo "## sorry/admit count"
  SORRIES=$(grep -rEn '\b(sorry|admit)\b' Jsp000661 --include='*.lean' | wc -l)
  echo "sorry_or_admit=$SORRIES"
  echo

  echo "## #print axioms"
  cat > /tmp/jsp_axioms.lean <<'EOF'
import Jsp000661.Main
#print axioms SimpleGraph.indepNumber_of_locally_large
EOF
  echo '```'
  lake env lean /tmp/jsp_axioms.lean 2>&1
  echo '```'
  echo

  if [ "$BUILD" -eq 0 ] && [ "$SORRIES" -eq 0 ]; then
    echo "**RESULT: GREEN**"
  else
    echo "**RESULT: RED**"
  fi
} | tee "$LOG"
