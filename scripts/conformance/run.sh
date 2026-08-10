#!/usr/bin/env bash
# Regenerate docs/CONFORMANCE.md from a real OpenACR checkout.
#
#   scripts/conformance/run.sh [path-to-data/dmmeta]
#
# The verdicts come from `amcc --conformance`, which is Lean; the two Python
# scripts slice the corpus and count rows. Nothing here decides anything.
set -euo pipefail
cd "$(dirname "$0")/../.."

corpus="${1:-$HOME/openacr-mine/data/dmmeta}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

lake build amcc >/dev/null

python3 scripts/conformance/slice.py "$corpus" -o "$tmp/modelled.ssim"
python3 scripts/conformance/slice.py "$corpus" --all-heads -o "$tmp/all.ssim"

lake exe amcc --conformance "$tmp/modelled.ssim" > "$tmp/modelled.tsv"
lake exe amcc --conformance "$tmp/all.ssim"      > "$tmp/all.tsv"

python3 scripts/conformance/tally.py "$tmp/modelled.tsv" "$tmp/all.tsv" \
  --corpus "$corpus" -o docs/CONFORMANCE.md
