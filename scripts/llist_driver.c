/* Differential driver for the generated intrusive doubly-linked list (`zdl`).
 *
 * Exercises the laws Amcc/Templates/Llist.lean states: Init empties the list,
 * Insert links at the head and is a no-op on a row already in, Remove unlinks
 * and is a no-op on a row already out, the count tracks membership, and
 * Insert-then-Remove is the identity on the list. Removing from the head, the
 * middle and the tail are separate cases because they take different branches
 * of the unlink.
 *
 * The expected output is transcribed from those statements, so a diff failure
 * means the emitted C does not do what the Lean theorems say it does.
 */
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

typedef struct task_row {
  uint64_t id;
  struct task_row *zdl_todo_next;
  struct task_row *zdl_todo_prev;
  bool zdl_todo_inlist;
} task_row;

void       TaskDb_zdl_todo_Init(void);
void       TaskDb_zdl_todo_Insert(struct task_row *row);
void       TaskDb_zdl_todo_Remove(struct task_row *row);
task_row*  TaskDb_zdl_todo_First(void);
task_row*  TaskDb_zdl_todo_Next(struct task_row *row);
task_row*  TaskDb_zdl_todo_Prev(struct task_row *row);
bool       TaskDb_zdl_todo_InLlistQ(struct task_row *row);
bool       TaskDb_zdl_todo_EmptyQ(void);
uint32_t   TaskDb_zdl_todo_N(void);

static void pb(bool b)    { printf("%u\n", b ? 1u : 0u); }
static void pu(uint32_t v){ printf("%u\n", (unsigned)v); }

/* Print the ids along the chain from the head, then the count. */
static void chain(void) {
  task_row *p = TaskDb_zdl_todo_First();
  while (p) { printf("%llu ", (unsigned long long)p->id); p = TaskDb_zdl_todo_Next(p); }
  printf("| %u\n", (unsigned)TaskDb_zdl_todo_N());
}

int main(void) {
  task_row a = {1, NULL, NULL, false};
  task_row b = {2, NULL, NULL, false};
  task_row c = {3, NULL, NULL, false};

  TaskDb_zdl_todo_Init();
  pb(TaskDb_zdl_todo_EmptyQ());          /* 1 */
  pu(TaskDb_zdl_todo_N());               /* 0 */
  pb(TaskDb_zdl_todo_First() == NULL);   /* 1 */

  /* Head insertion, so the chain comes out reversed. */
  TaskDb_zdl_todo_Insert(&a);
  TaskDb_zdl_todo_Insert(&b);
  TaskDb_zdl_todo_Insert(&c);
  chain();                               /* 3 2 1 | 3 */
  pb(TaskDb_zdl_todo_EmptyQ());          /* 0 */
  pb(TaskDb_zdl_todo_InLlistQ(&a));      /* 1 */

  /* prev is the inverse of next. */
  pb(TaskDb_zdl_todo_Prev(&c) == NULL);  /* 1 -- c is the head */
  pb(TaskDb_zdl_todo_Prev(&b) == &c);    /* 1 */
  pb(TaskDb_zdl_todo_Prev(&a) == &b);    /* 1 */
  pb(TaskDb_zdl_todo_Next(&a) == NULL);  /* 1 -- a is the tail */

  /* Insert on a row already in the list is a no-op. */
  TaskDb_zdl_todo_Insert(&b);
  chain();                               /* 3 2 1 | 3 */

  /* Remove from the middle: both neighbours relink. */
  TaskDb_zdl_todo_Remove(&b);
  chain();                               /* 3 1 | 2 */
  pb(TaskDb_zdl_todo_InLlistQ(&b));      /* 0 */
  pb(TaskDb_zdl_todo_Prev(&a) == &c);    /* 1 */

  /* Remove on a row already out is a no-op. */
  TaskDb_zdl_todo_Remove(&b);
  chain();                               /* 3 1 | 2 */

  /* Remove the head: the head advances. */
  TaskDb_zdl_todo_Remove(&c);
  chain();                               /* 1 | 1 */
  pb(TaskDb_zdl_todo_Prev(&a) == NULL);  /* 1 */

  /* Remove the tail: the list empties. */
  TaskDb_zdl_todo_Remove(&a);
  chain();                               /* | 0 */
  pb(TaskDb_zdl_todo_EmptyQ());          /* 1 */

  /* Insert-then-Remove is the identity on the list. */
  TaskDb_zdl_todo_Insert(&a);
  TaskDb_zdl_todo_Insert(&b);
  TaskDb_zdl_todo_Insert(&c);
  TaskDb_zdl_todo_Remove(&c);
  chain();                               /* 2 1 | 2 */
  TaskDb_zdl_todo_Insert(&c);
  TaskDb_zdl_todo_Remove(&c);
  chain();                               /* 2 1 | 2 */
  return 0;
}
