#!/usr/bin/env python3
"""Concatenate the parts of an OpenACR `data/dmmeta` directory that AMCC models.

A dev tool, and deliberately dumb: it decides nothing. Every verdict in the
report comes from `Ssim.Conformance` on the Lean side, which uses the shipping
reader, the shipping `supported` list and the shipping `Dmmeta.isCIdent`. If
this script disappeared the verdicts would be unchanged; only the slicing and
the tallying would have to be done by hand.

The `--all-heads` form includes every ssimfile in the directory, so the report
can also say how much of `data/dmmeta` AMCC does not model *at all* — that
number is otherwise invisible, because the heads we do read are a tiny
fraction of the corpus.
"""
import argparse
import pathlib
import sys

# The heads AMCC's reader models. Everything else is counted, not read.
MODELLED = ["ctype.ssim", "field.ssim", "inlary.ssim", "smallstr.ssim"]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("dmmeta", help="path to data/dmmeta")
    ap.add_argument("--all-heads", action="store_true",
                    help="include every ssimfile, not just the modelled ones")
    ap.add_argument("-o", "--out", required=True)
    args = ap.parse_args()

    root = pathlib.Path(args.dmmeta)
    if not root.is_dir():
        print(f"{root}: not a directory", file=sys.stderr)
        return 1

    if args.all_heads:
        files = sorted(root.glob("*.ssim"))
    else:
        files = [root / n for n in MODELLED]

    out = []
    for f in files:
        if not f.exists():
            print(f"{f}: missing, skipped", file=sys.stderr)
            continue
        out.append(f.read_text())

    pathlib.Path(args.out).write_text("".join(out))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
