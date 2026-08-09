import Amcc.Codegen.Print
import Amcc.Templates.ArrayTable

/-!
# AMCC — Phase 4: the printer, exercised

Golden tests: the printed C for the example schemas, byte for byte. The
printer is a trusted component, so these checks are its whole regression
story inside `lake build` — a change to the printed output fails here and
must be a conscious decision. (The behavioural check — that the printed C
*compiles and computes the same answers* as `execStmt` — cannot run inside
`lake build`; that is `scripts/smoke.sh`.)

The small `rfl` checks pin the declarator recursion, which is the one piece
of the printer with actual room to be wrong (C's inside-out declarator
syntax); the full-program golden is `#guard`, since a kilobyte-scale string
equality has no business in kernel reduction.
-/

namespace Codegen
namespace PrintChecks

open CSubset Templates.ArrayTable

/-! ## The declarator recursion, kernel-checked -/

/-- checked by: `lake build` -/
example : Print.declare (.scalar .u32) "x" = "uint32_t x" := rfl

/-- Arrays extend the declarator left to right. -/
example : Print.declare (.arr (.arr (.scalar .u64) 3) 2) "m"
    = "uint64_t m[2][3]" := rfl

/-- A plain pointer needs no parentheses. -/
example : Print.declare (.ptr (.strct "order_row")) "p"
    = "order_row *p" := rfl

/-- Pointer *to an array* does, or `*p[2]` would bind as an array of
pointers. -/
example : Print.declare (.ptr (.arr (.scalar .u64) 2)) "p"
    = "uint64_t (*p)[2]" := rfl

/-- Literal suffixes: no integer literal has a surprising promoted type. -/
example : Print.lit (.u32 4) = "4u" := rfl
example : Print.lit (.u64 0) = "0ull" := rfl

/-! ## The full translation unit for `orders`, byte for byte -/

private def ordersGolden : String :=
"#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

typedef struct {
  uint64_t id;
  uint64_t price;
  uint64_t qty;
  bool occupied;
} order_row;

static order_row g_order[4];

order_row *order_Find(uint64_t id) {
  uint32_t _i = 0u;
  for (_i = 0u; _i < 4u; ++_i) {
    if ((g_order[_i].occupied && (g_order[_i].id == id))) {
      return (&g_order[_i]);
    }
  }
  return NULL;
}

bool order_InsertMaybe(uint64_t id, uint64_t price, uint64_t qty) {
  order_row *_at = NULL;
  uint32_t _j = 0u;
  _at = order_Find(id);
  if ((_at != NULL)) {
    _at->price = price;
    _at->qty = qty;
    return true;
  }
  for (_j = 0u; _j < 4u; ++_j) {
    if ((!g_order[_j].occupied)) {
      g_order[_j].occupied = true;
      g_order[_j].id = id;
      g_order[_j].price = price;
      g_order[_j].qty = qty;
      return true;
    }
  }
  return false;
}

bool order_Remove(uint64_t id) {
  order_row *_at = NULL;
  _at = order_Find(id);
  if ((_at != NULL)) {
    _at->occupied = false;
    return true;
  }
  return false;
}
"

/- checked by: `lake build` (compiled `#guard`, not kernel `rfl`) -/
#guard Print.program (genC Schema.Examples.orders) == ordersGolden

/- The degenerate schema — no value fields, so no getters and an insert whose
present-key branch rewrites nothing. checked by: `lake build` -/
#guard Print.program (genC Schema.Examples.keysOnly)
    == "#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

typedef struct {
  uint32_t k;
  bool occupied;
} tag_row;

static tag_row g_tag[2];

tag_row *tag_Find(uint32_t k) {
  uint32_t _i = 0u;
  for (_i = 0u; _i < 2u; ++_i) {
    if ((g_tag[_i].occupied && (g_tag[_i].k == k))) {
      return (&g_tag[_i]);
    }
  }
  return NULL;
}

bool tag_InsertMaybe(uint32_t k) {
  tag_row *_at = NULL;
  uint32_t _j = 0u;
  _at = tag_Find(k);
  if ((_at != NULL)) {
    return true;
  }
  for (_j = 0u; _j < 2u; ++_j) {
    if ((!g_tag[_j].occupied)) {
      g_tag[_j].occupied = true;
      g_tag[_j].k = k;
      return true;
    }
  }
  return false;
}

bool tag_Remove(uint32_t k) {
  tag_row *_at = NULL;
  _at = tag_Find(k);
  if ((_at != NULL)) {
    _at->occupied = false;
    return true;
  }
  return false;
}
"

end PrintChecks
end Codegen
