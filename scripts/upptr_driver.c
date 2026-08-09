/* Differential driver for the generated `Upptr` accessors.
 *
 * Exercises exactly the laws Amcc/Templates/Upptr.lean proves:
 *
 *   init_correct  Init leaves the up-pointer NULL, and touches nothing else.
 *   get_set       Get after Set returns exactly what was Set (read-back),
 *                 and the Set is invisible at every non-overlapping path.
 *   test_null     Q is false on NULL.
 *   test_ptr      Q is true on a pointer.
 *
 * The expected output is transcribed from those statements, so a diff failure
 * means the emitted C does not do what the Lean theorems say it does.
 */
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

typedef struct level_row {
  uint64_t price;
} level_row;

typedef struct child_row {
  uint64_t id;
  struct level_row *p_level;
} child_row;

void        child_row_p_level_Init(struct child_row *row);
level_row*  child_row_p_level_Get(struct child_row *row);
void        child_row_p_level_Set(struct child_row *row, struct level_row *p);
bool        child_row_p_level_Q(struct child_row *row);

static void pb(bool b) { printf("%u\n", b ? 1u : 0u); }

int main(void) {
  level_row parent_a = { 100 }, parent_b = { 200 };
  child_row kid = { 7, (struct level_row *)&parent_b };  /* deliberate junk */
  child_row other = { 9, NULL };

  /* init_correct: the field is NULL afterwards, whatever it held before. */
  child_row_p_level_Init(&kid);
  pb(child_row_p_level_Get(&kid) == NULL);   /* 1 */
  pb(child_row_p_level_Q(&kid));             /* 0 -- test_null */
  pb(kid.id == 7);                           /* 1 -- frame: the key survived */

  /* get_set: read-back. */
  child_row_p_level_Set(&kid, &parent_a);
  pb(child_row_p_level_Get(&kid) == &parent_a);  /* 1 */
  pb(child_row_p_level_Q(&kid));                 /* 1 -- test_ptr */

  /* Overwriting returns the new value, not the old. */
  child_row_p_level_Set(&kid, &parent_b);
  pb(child_row_p_level_Get(&kid) == &parent_b);  /* 1 */

  /* Frame: a Set through one row is invisible through a non-overlapping one. */
  child_row_p_level_Init(&other);
  child_row_p_level_Set(&kid, &parent_a);
  pb(child_row_p_level_Get(&other) == NULL);     /* 1 */
  pb(kid.id == 7 && other.id == 9);              /* 1 */
  pb(parent_a.price == 100 && parent_b.price == 200); /* 1 -- parents untouched */

  /* Init is idempotent, and undoes a Set. */
  child_row_p_level_Init(&kid);
  child_row_p_level_Init(&kid);
  pb(child_row_p_level_Q(&kid));                 /* 0 */
  return 0;
}
