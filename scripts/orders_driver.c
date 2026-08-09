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

/* amc-shaped API: Find hands back the row, NULL when absent. The row struct
 * is redeclared here exactly as the generator emits it, so the driver reads
 * fields the way a real consumer would. */
typedef struct {
  uint64_t id;
  uint64_t price;
  uint64_t qty;
  bool occupied;
} order_row;

order_row* order_Find(uint64_t id);
bool       order_InsertMaybe(uint64_t id, uint64_t price, uint64_t qty);
bool       order_Remove(uint64_t id);

static void pb(bool b)      { printf("%u\n", (unsigned)b); }
static void pu64(uint64_t v){ printf("%llu\n", (unsigned long long)v); }
/* 1 when the key is present, 0 when Find returned NULL */
static void pfound(const order_row *r) { printf("%u\n", r ? 1u : 0u); }
/* a field read through the pointer, or a stated miss */
static void pfield(const order_row *r, int which) {
  if (!r) { printf("absent\n"); return; }
  pu64(which == 0 ? r->price : r->qty);
}

int main(void) {
  /* Sequence A: insert, look up, read fields, erase, confirm gone. */
  pb(order_InsertMaybe(7, 100, 5));
  pfound(order_Find(7));
  pfield(order_Find(7), 0);
  pfield(order_Find(7), 1);
  pfound(order_Find(8));
  pb(order_Remove(7));
  pfound(order_Find(7));
  pfield(order_Find(7), 0);   /* absent is now distinguishable from zero */

  /* Sequence B: fill the table, watch it refuse, erase, reclaim the slot. */
  pb(order_InsertMaybe(1, 10, 1));
  pb(order_InsertMaybe(2, 20, 2));
  pb(order_InsertMaybe(3, 30, 3));
  pb(order_InsertMaybe(4, 40, 4));
  pb(order_InsertMaybe(5, 50, 5));
  pb(order_Remove(2));
  pb(order_InsertMaybe(5, 50, 5));
  pfield(order_Find(5), 0);

  return 0;
}
