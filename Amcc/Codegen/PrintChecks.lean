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

/-- A pointer wraps the declarator, so pointer-to-array parenthesises. -/
example : Print.declare (.ptr (.strct "order_row")) "p"
    = "order_row (*p)" := rfl

/-- Literal suffixes: no integer literal has a surprising promoted type. -/
example : Print.lit (.u32 4) = "4u" := rfl
example : Print.lit (.u64 0) = "0ull" := rfl

/-! ## The full translation unit for `orders`, byte for byte -/

private def ordersGolden : String :=
"#include <stdint.h>
#include <stdbool.h>

typedef struct {
  uint64_t id;
  uint64_t price;
  uint64_t qty;
  bool occupied;
} order_row;

static order_row g_order[4];

uint32_t order_find(uint64_t id) {
  uint32_t _i = 0u;
  for (_i = 0u; _i < 4u; ++_i) {
    if ((g_order[_i].occupied && (g_order[_i].id == id))) {
      return _i;
    }
  }
  return 4u;
}

bool order_insert(uint64_t id, uint64_t price, uint64_t qty) {
  uint32_t _at = 0u;
  uint32_t _j = 0u;
  _at = order_find(id);
  if ((_at != 4u)) {
    g_order[_at].price = price;
    g_order[_at].qty = qty;
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

bool order_erase(uint64_t id) {
  uint32_t _at = 0u;
  _at = order_find(id);
  if ((_at != 4u)) {
    g_order[_at].occupied = false;
    return true;
  }
  return false;
}

uint64_t order_get_price(uint64_t id) {
  uint32_t _at = 0u;
  _at = order_find(id);
  if ((_at != 4u)) {
    return g_order[_at].price;
  }
  return 0ull;
}

uint64_t order_get_qty(uint64_t id) {
  uint32_t _at = 0u;
  _at = order_find(id);
  if ((_at != 4u)) {
    return g_order[_at].qty;
  }
  return 0ull;
}
"

/- checked by: `lake build` (compiled `#guard`, not kernel `rfl`) -/
#guard Print.program (genC Schema.Examples.orders) == ordersGolden

/- The degenerate schema — no value fields, so no getters and an insert whose
present-key branch rewrites nothing. checked by: `lake build` -/
#guard Print.program (genC Schema.Examples.keysOnly)
    == "#include <stdint.h>
#include <stdbool.h>

typedef struct {
  uint32_t k;
  bool occupied;
} tag_row;

static tag_row g_tag[2];

uint32_t tag_find(uint32_t k) {
  uint32_t _i = 0u;
  for (_i = 0u; _i < 2u; ++_i) {
    if ((g_tag[_i].occupied && (g_tag[_i].k == k))) {
      return _i;
    }
  }
  return 2u;
}

bool tag_insert(uint32_t k) {
  uint32_t _at = 0u;
  uint32_t _j = 0u;
  _at = tag_find(k);
  if ((_at != 2u)) {
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

bool tag_erase(uint32_t k) {
  uint32_t _at = 0u;
  _at = tag_find(k);
  if ((_at != 2u)) {
    g_tag[_at].occupied = false;
    return true;
  }
  return false;
}
"

end PrintChecks
end Codegen
