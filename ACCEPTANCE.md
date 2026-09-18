# ACCEPTANCE — JSP-000661

All gates must hold on the `main` branch.

## Gates

1. `lake build` completes green on the pinned toolchain (`lean-toolchain`,
   `leanprover/lean4:v4.34.0`) with Mathlib pinned at `v4.34.0`.
2. Zero `sorry` / `admit` in the development
   (checked by `scripts/harness.sh` over `Jsp000661/**/*.lean`).
3. `#print axioms indepNumber_of_locally_large` reports exactly the three Lean
   axioms: `Classical.choice`, `Quot.sound`, `propext` (no `sorryAx`, no custom
   axioms).
4. The repository is public, and the claim records the full 40-character commit
   SHA of the accepted build.
5. `scripts/harness.sh` output is committed to `HARNESS_LOG.md` after every merge
   to `main`.

## Headline theorem

`Jsp000661.Main.indepNumber_of_locally_large` — see `PROBLEM.md` for the exact
statement and its correspondence to Alon–Sudakov Theorem 2.2.
