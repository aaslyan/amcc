#!/usr/bin/env bash
# Differential smoke test: the printed C, compiled by a real C compiler,
# must answer the ArrayTableChecks call sequences exactly as the Lean
# semantics does. This is the check `lake build` cannot run (it needs a C
# toolchain), and it is the entire empirical link between `execStmt` and
# the C the generator ships.
#
# Three things are checked per template:
#   1. single-file mode  — one translation unit, compiled with its driver
#   2. split mode        — <name>_gen.c compiled with -I on the header dir
#   3. header-alone      — a translation unit that includes ONLY the header,
#                          which is what makes the header a usable interface
#                          rather than a fragment of the implementation
# All three pass -Wall -Wextra -Werror. Modes 1 and 2 must produce byte-identical
# output, and both must match the transcribed expectations.
#
# The split files are also diffed against the goldens under scripts/gen/, so a
# change in the emitted layout shows up as a reviewable diff rather than as
# nothing at all.
set -euo pipefail
cd "$(dirname "$0")/.."

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

CFLAGS=(-std=c11 -Wall -Wextra -Werror)

lake build amcc >/dev/null

# --- the split output, once, for every template ------------------------------
lake exe amcc all --out "$tmp/gen" 2>/dev/null
diff -r scripts/gen "$tmp/gen"
echo "smoke: gen    OK — the split output matches the goldens under scripts/gen"

# check <name>: run the single-file build, the split build and the header-alone
# build, and diff every answer against the transcribed expectations.
check() {
  local name="$1" driver="$2" expected="$3" blurb="$4"

  # 1. single file, on stdout — the original mode
  lake exe amcc "$name" > "$tmp/$name.c"
  cc "${CFLAGS[@]}" -o "$tmp/${name}_one" "$tmp/$name.c" "$driver"
  "$tmp/${name}_one" > "$tmp/${name}_one.txt"
  diff "$expected" "$tmp/${name}_one.txt"

  # 2. the split build: the .c includes the .h, found via -I
  cc "${CFLAGS[@]}" -I"$tmp/gen" -o "$tmp/${name}_split" \
    "$tmp/gen/${name}_gen.c" "$driver"
  "$tmp/${name}_split" > "$tmp/${name}_split.txt"
  diff "$expected" "$tmp/${name}_split.txt"

  # ...and the two modes must agree with each other, not merely each with the
  # expectations, so a change that broke both identically still shows up above.
  diff "$tmp/${name}_one.txt" "$tmp/${name}_split.txt"

  # 3. the header alone: nothing but the #include, compiled to an object.
  printf '#include "%s_gen.h"\n' "$name" > "$tmp/${name}_hdr_only.c"
  cc "${CFLAGS[@]}" -I"$tmp/gen" -c -o "$tmp/${name}_hdr_only.o" \
    "$tmp/${name}_hdr_only.c"

  echo "smoke: ${name} OK — $blurb"
}

check orders scripts/orders_driver.c scripts/orders_expected.txt \
  "compiled C agrees with the Lean semantics; header stands alone"
check pool scripts/pool_driver.c scripts/pool_expected.txt \
  "allocation, reuse and exhaustion behave as proved; header stands alone"
check upptr scripts/upptr_driver.c scripts/upptr_expected.txt \
  "read-back and frame hold in the compiled C; header stands alone"
check llist scripts/llist_driver.c scripts/llist_expected.txt \
  "link, unlink and the idempotence guards behave as proved; header stands alone"
# Keys 1, 9 and 17 collide, so the chain cases are real.
check thash scripts/thash_driver.c scripts/thash_expected.txt \
  "find, duplicate refusal and chain unlink behave as stated; header stands alone"
