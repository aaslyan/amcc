/* Differential driver for the generated free-list pool.
 *
 * Exercises the properties Amcc/Spec/Pool.lean proves about the algorithm:
 * allocation hands out distinct live slots, freeing returns one for reuse,
 * exhaustion reports NULL rather than trapping, and the count tracks the
 * live set. The expected output is transcribed from those properties, so a
 * diff failure means the emitted C does not implement the algorithm the model
 * describes.
 */
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

typedef struct order_row {
  uint64_t id; uint64_t price; uint64_t qty;
  struct order_row *_freenext;
} order_row;

void       OrderDb_row_Init(void);
order_row* OrderDb_row_Alloc(void);
void       OrderDb_row_Free(order_row *p);
uint32_t   OrderDb_row_N(void);

static void pu(uint32_t v)          { printf("%u\n", (unsigned)v); }
static void pp(const order_row *r)  { printf("%u\n", r ? 1u : 0u); }

int main(void) {
  order_row *a, *b, *c, *d, *e;
  OrderDb_row_Init();
  pu(OrderDb_row_N());                 /* 0 */

  a = OrderDb_row_Alloc(); pp(a);      /* 1 */
  b = OrderDb_row_Alloc(); pp(b);      /* 1 */
  c = OrderDb_row_Alloc(); pp(c);      /* 1 */
  d = OrderDb_row_Alloc(); pp(d);      /* 1 */
  pu(OrderDb_row_N());                 /* 4 */

  e = OrderDb_row_Alloc(); pp(e);      /* 0 -- exhausted, NULL not a trap */

  /* distinct slots */
  printf("%u\n", (unsigned)(a != b && b != c && c != d && a != d));

  /* payload written through one pointer is not disturbed by the others */
  a->price = 111; b->price = 222; c->price = 333; d->price = 444;
  printf("%llu\n", (unsigned long long)a->price);

  OrderDb_row_Free(b);
  pu(OrderDb_row_N());                 /* 3 */

  e = OrderDb_row_Alloc(); pp(e);      /* 1 -- the freed slot is reusable */
  printf("%u\n", (unsigned)(e == b));  /* 1 -- and it is the one freed */
  pu(OrderDb_row_N());                 /* 4 */

  /* the other payloads survived the free/alloc round trip */
  printf("%llu\n", (unsigned long long)a->price);
  printf("%llu\n", (unsigned long long)d->price);
  return 0;
}
