#!/usr/bin/env bash
# Differential smoke test: the printed C, compiled by a real C compiler,
# must answer the ArrayTableChecks call sequences exactly as the Lean
# semantics does. This is the check `lake build` cannot run (it needs a C
# toolchain), and it is the entire empirical link between `execStmt` and
# the C the generator ships.
set -euo pipefail
cd "$(dirname "$0")/.."

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

lake build amcc >/dev/null
lake exe amcc orders > "$tmp/order_table.c"

cc -std=c11 -Wall -Wextra -Werror -o "$tmp/smoke" \
  "$tmp/order_table.c" scripts/orders_driver.c

"$tmp/smoke" > "$tmp/got.txt"
diff scripts/orders_expected.txt "$tmp/got.txt"
echo "smoke: table  OK — compiled C agrees with the Lean semantics"

# The pool template, against the properties Spec/Pool.lean proves.
lake exe amcc pool > "$tmp/pool.c"
cc -std=c11 -Wall -Wextra -Werror -o "$tmp/pool" "$tmp/pool.c" scripts/pool_driver.c
"$tmp/pool" > "$tmp/pool_got.txt"
diff scripts/pool_expected.txt "$tmp/pool_got.txt"
echo "smoke: pool   OK — allocation, reuse and exhaustion behave as proved"

# The Upptr accessors, against the laws Templates/Upptr.lean proves.
lake exe amcc upptr > "$tmp/upptr.c"
cc -std=c11 -Wall -Wextra -Werror -o "$tmp/upptr" "$tmp/upptr.c" scripts/upptr_driver.c
"$tmp/upptr" > "$tmp/upptr_got.txt"
diff scripts/upptr_expected.txt "$tmp/upptr_got.txt"
echo "smoke: upptr  OK — read-back and frame hold in the compiled C"

# The intrusive list, against the laws Templates/Llist.lean states.
lake exe amcc llist > "$tmp/llist.c"
cc -std=c11 -Wall -Wextra -Werror -o "$tmp/llist" "$tmp/llist.c" scripts/llist_driver.c
"$tmp/llist" > "$tmp/llist_got.txt"
diff scripts/llist_expected.txt "$tmp/llist_got.txt"
echo "smoke: llist  OK — link, unlink and the idempotence guards behave as proved"

# The hash index. Keys 1, 9 and 17 collide, so the chain cases are real.
lake exe amcc thash > "$tmp/thash.c"
cc -std=c11 -Wall -Wextra -Werror -o "$tmp/thash" "$tmp/thash.c" scripts/thash_driver.c
"$tmp/thash" > "$tmp/thash_got.txt"
diff scripts/thash_expected.txt "$tmp/thash_got.txt"
echo "smoke: thash  OK — find, duplicate refusal and chain unlink behave as stated"
