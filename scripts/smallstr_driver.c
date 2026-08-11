/* Differential driver for the generated `Smallstr` (`rpascal`) operations.
 *
 * Exercises exactly what Amcc/Templates/Smallstr.lean says, and one thing it
 * says about the *representation* rather than about the C:
 *
 *   Init         leaves the count zero.
 *   N            reports the count.
 *   Max          is the declared length, not the array size.
 *   Add          appends when there is room, and does nothing when full —
 *                which is `absRpascal ch n ++ [c]` at the abstract level.
 *   absRpascal   the first `n` bytes are the value; the rest of the array,
 *                including the dead `ch[N]`, is not.
 *
 * The last one is why the array is 17 and not 16: amc sizes an rpascal array
 * `N + 1` and never writes the last element. This driver checks that it stays
 * unwritten after filling the string to capacity.
 *
 * The expected output is transcribed from those statements, so a diff failure
 * means the emitted C does not do what the Lean statements say it does.
 */
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>

typedef struct name_row {
  uint64_t id;
  uint8_t ch[17];
  uint8_t n_ch;
} name_row;

void     name_row_ch_Init(struct name_row *row);
uint8_t  name_row_ch_N(struct name_row *row);
uint32_t name_row_ch_Max(void);
void     name_row_ch_Add(struct name_row *row, uint8_t c);

/* `absRpascal ch n` — the first n bytes, printed. */
static void show(const char *tag, struct name_row *row) {
  uint8_t n = name_row_ch_N(row);
  printf("%s n=%u abs=\"", tag, (unsigned)n);
  for (uint8_t i = 0; i < n; i++) putchar((int)row->ch[i]);
  printf("\"\n");
}

int main(void) {
  struct name_row row;
  memset(&row, 0xEE, sizeof row);   /* nothing may be assumed pre-zeroed */

  /* Init: the count is zero, so the abstraction is empty whatever the array
     holds. */
  name_row_ch_Init(&row);
  show("init  ", &row);

  /* Max is the declared length. */
  printf("max    %u\n", (unsigned)name_row_ch_Max());

  /* Add appends: abs becomes abs ++ [c], one byte at a time. */
  name_row_ch_Add(&row, (uint8_t)'a');
  show("add a ", &row);
  name_row_ch_Add(&row, (uint8_t)'b');
  show("add b ", &row);
  name_row_ch_Add(&row, (uint8_t)'c');
  show("add c ", &row);

  /* Fill to capacity. 3 already in, 13 to go. */
  for (int i = 0; i < 13; i++) name_row_ch_Add(&row, (uint8_t)('0' + (i % 10)));
  show("full  ", &row);

  /* Full: Add does nothing. The count does not move and neither does the
     string — this is the `n = N` no-op branch of the guard. */
  name_row_ch_Add(&row, (uint8_t)'Z');
  show("add Z ", &row);

  /* And the dead byte amc allocates but never writes is still what we put
     there before Init. `Add` guards on `< N`, so `ch[N]` is out of its
     reach with a whole element to spare. */
  printf("dead   %u\n", (unsigned)row.ch[16]);

  /* Re-Init throws the string away without touching the array. */
  name_row_ch_Init(&row);
  show("reinit", &row);

  return 0;
}
