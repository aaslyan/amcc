/* Differential driver for the generated `orders` table.
 *
 * Replays the two call sequences that `Amcc/Templates/ArrayTableChecks.lean`
 * runs against the Lean semantics (`runCalls`), one result per line. The
 * expected output, `orders_expected.txt`, is transcribed from the checked
 * Lean answers — so a diff failure means the printed C, compiled by a real
 * C compiler, disagrees with `execStmt`.
 *
 * Sequence B runs after sequence A in the same process; that is equivalent
 * to a fresh table because A ends with its only key erased, and a table
 * whose occupancy flags are all false is observationally the zero table:
 * `find` tests the flag before the key, and a claiming `insert` overwrites
 * every field.
 */
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

uint32_t order_find(uint64_t id);
bool     order_insert(uint64_t id, uint64_t price, uint64_t qty);
bool     order_erase(uint64_t id);
uint64_t order_get_price(uint64_t id);
uint64_t order_get_qty(uint64_t id);

static void pb(bool b)      { printf("%u\n", (unsigned)b); }
static void pu32(uint32_t v){ printf("%u\n", (unsigned)v); }
static void pu64(uint64_t v){ printf("%llu\n", (unsigned long long)v); }

int main(void) {
  /* Sequence A: insert, look up, read fields, erase, confirm gone. */
  pb(order_insert(7, 100, 5));
  pu32(order_find(7));
  pu64(order_get_price(7));
  pu64(order_get_qty(7));
  pu32(order_find(8));
  pb(order_erase(7));
  pu32(order_find(7));
  pu64(order_get_price(7));

  /* Sequence B: fill the table, watch it refuse, erase, reclaim the slot. */
  pb(order_insert(1, 10, 1));
  pb(order_insert(2, 20, 2));
  pb(order_insert(3, 30, 3));
  pb(order_insert(4, 40, 4));
  pb(order_insert(5, 50, 5));
  pb(order_erase(2));
  pb(order_insert(5, 50, 5));
  pu32(order_find(5));

  return 0;
}
