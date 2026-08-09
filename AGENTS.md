# Repository Guidelines

## Project Structure & Module Organization

This is a Lean 4/Lake project for AMCC, a verified schema-to-C generator. The
library root is `Amcc.lean`; every module that should be proof-checked by
`lake build` must be imported there. Source modules live under `Amcc/`.

- `Amcc/CSubset/`: syntax, semantics, well-formedness, examples, and sanity
  theorems for the restricted C subset.
- `Amcc/Schema.lean` and `Amcc/Interface.lean`: schema DSL and public-facing
  interface.
- `Amcc/Templates/`: generator templates and template checks.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: Lake package and
  pinned Lean toolchain metadata.

There is no separate `test/` directory. Regression checks are Lean modules such
as `Amcc/CSubset/WfChecks.lean` and `Amcc/Templates/ArrayTableChecks.lean`.

## Build, Test, and Development Commands

- `lake build`: builds the `Amcc` library and checks all imported proofs and
  `example ... := rfl` regressions.
- `lake env lean Amcc/CSubset/WfChecks.lean`: checks one Lean file in the Lake
  environment.
- `lake clean`: removes Lake build artifacts when a stale build is suspected.

Use the Lean version pinned in `lean-toolchain` (`leanprover/lean4:v4.26.0`).

## Coding Style & Naming Conventions

Follow the existing Lean style: two-space indentation in declarations and match
arms, descriptive theorem and definition names, and namespaces matching their
directory path. Use PascalCase for inductive types and structures
(`ScalarTy`, `Program`) and lower camel case for definitions and examples
(`execStmt`, `tinyTable`, `pMissingReturn`).

Keep module docstrings useful and specific. Prefer small, structural Lean
definitions over ad hoc string logic when working with syntax, schemas, or
checks.

## Testing Guidelines

Treat `lake build` as the main verification signal. Add new behavioral
regressions as Lean `example` declarations, usually in a `*Checks.lean` module,
and make them computational when possible with `:= rfl`. For negative checker
cases, assert the exact error list so weakened validation fails visibly.

When adding a new module that must be verified, import it from `Amcc.lean`.

## Commit & Pull Request Guidelines

No Git history is available in this checkout, so no existing commit convention
can be inferred. Use concise imperative commit subjects, for example
`Add schema validation checks`.

Pull requests should explain the proof or generator behavior changed, list the
commands run, and call out any new module that was added to `Amcc.lean`.
