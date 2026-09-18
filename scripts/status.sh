#!/usr/bin/env bash
# Structured status snapshot.
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
echo "sha=$(git rev-parse --short HEAD 2>/dev/null || echo none)"
echo "branch=$(git branch --show-current)"
echo "uncommitted=$(git status --porcelain | wc -l | tr -d ' ')"
echo "sorries=$(grep -rEn '\b(sorry|admit)\b' Jsp000661 --include='*.lean' 2>/dev/null | wc -l | tr -d ' ')"
echo "lean_files=$(find Jsp000661 -name '*.lean' | wc -l | tr -d ' ')"
if [ -f HARNESS_LOG.md ]; then
  echo "last_harness=$(grep -m1 'RESULT' HARNESS_LOG.md || echo none)"
fi
