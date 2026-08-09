/* Differential driver for the generated hash index.
 *
 * Exercises: Init empties every bucket, InsertMaybe indexes a row and refuses
 * a duplicate key, Find locates by key and reports NULL for an absent one,
 * Remove unlinks from the head, the middle and the tail of a bucket chain, and
 * the count tracks membership. Keys 1, 9 and 17 collide (all are 1 mod 8), so
 * the chain cases are real rather than hypothetical.
 */
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

typedef struct item_row {
  uint32_t id;
  uint32_t qty;
  struct item_row *ind_item_next;
  bool ind_item_inhash;
} item_row;

void      ItemDb_ind_item_Init(void);
item_row* ItemDb_ind_item_Find(uint32_t key);
bool      ItemDb_ind_item_InsertMaybe(struct item_row *row);
void      ItemDb_ind_item_Remove(struct item_row *row);
uint32_t  ItemDb_ind_item_N(void);

static void pb(bool b)     { printf("%u\n", b ? 1u : 0u); }
static void pu(uint32_t v) { printf("%u\n", (unsigned)v); }
static void pf(uint32_t k) {
  item_row *r = ItemDb_ind_item_Find(k);
  if (r) printf("%u:%u\n", (unsigned)r->id, (unsigned)r->qty);
  else   printf("-\n");
}

int main(void) {
  /* 1, 9, 17 all land in bucket 1; 2 lands in bucket 2. */
  item_row a = {1, 100, NULL, false};
  item_row b = {9, 200, NULL, false};
  item_row c = {17, 300, NULL, false};
  item_row d = {2, 400, NULL, false};
  item_row dup = {9, 999, NULL, false};

  ItemDb_ind_item_Init();
  pu(ItemDb_ind_item_N());              /* 0 */
  pf(1);                                /* - */

  pb(ItemDb_ind_item_InsertMaybe(&a));  /* 1 */
  pb(ItemDb_ind_item_InsertMaybe(&b));  /* 1 */
  pb(ItemDb_ind_item_InsertMaybe(&c));  /* 1 */
  pb(ItemDb_ind_item_InsertMaybe(&d));  /* 1 */
  pu(ItemDb_ind_item_N());              /* 4 */

  pf(1);   /* 1:100 */
  pf(9);   /* 9:200 */
  pf(17);  /* 17:300 */
  pf(2);   /* 2:400 */
  pf(5);   /* -  absent, and its bucket is empty */
  pf(25);  /* -  absent, but its bucket has three entries */

  /* A duplicate key is refused, and does not disturb the index. */
  pb(ItemDb_ind_item_InsertMaybe(&dup)); /* 0 */
  pu(ItemDb_ind_item_N());               /* 4 */
  pf(9);                                 /* 9:200 -- still the original */

  /* Inserting a row already in the index is refused too. */
  pb(ItemDb_ind_item_InsertMaybe(&a));   /* 0 */
  pu(ItemDb_ind_item_N());               /* 4 */

  /* Remove from the head of the chain (17 was inserted last). */
  ItemDb_ind_item_Remove(&c);
  pu(ItemDb_ind_item_N());               /* 3 */
  pf(17);                                /* - */
  pf(9);                                 /* 9:200 */
  pf(1);                                 /* 1:100 */

  /* Remove from the middle: put 17 back at the head first. */
  pb(ItemDb_ind_item_InsertMaybe(&c));   /* 1 */
  ItemDb_ind_item_Remove(&b);
  pu(ItemDb_ind_item_N());               /* 3 */
  pf(9);                                 /* - */
  pf(17);                                /* 17:300 */
  pf(1);                                 /* 1:100 */

  /* Remove from the tail. */
  ItemDb_ind_item_Remove(&a);
  pu(ItemDb_ind_item_N());               /* 2 */
  pf(1);                                 /* - */
  pf(17);                                /* 17:300 */

  /* Remove on a row not in the index is a no-op. */
  ItemDb_ind_item_Remove(&a);
  pu(ItemDb_ind_item_N());               /* 2 */

  /* And a removed row can be re-indexed. */
  pb(ItemDb_ind_item_InsertMaybe(&a));   /* 1 */
  pu(ItemDb_ind_item_N());               /* 3 */
  pf(1);                                 /* 1:100 */
  return 0;
}
