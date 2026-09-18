# SCOPE — what this formalization covers

## In scope

- Definitions: independence number `α(G)`, the local condition
  "every `s`-vertex induced subgraph has independence number ≥ `t`".
- **Theorem 2.2 (Alon–Sudakov), explicit quantitative form** — the lower-bound
  direction that answers the catalog question ("how large an independent set must
  the whole graph have?"). Formalized as `indepNumber_of_locally_large`
  (`Jsp000661/Main.lean`), giving for every `I` with `s^(2I−1) ≤ n` an independent
  set of size `≥ (t/2)·I`. For `s = Θ(log³ n)`, `t = Θ(log n)` this yields
  `α(G) ≥ Ω(log² n / log log n)`, matching the paper's `q(n)` lower bound.

## Out of scope (documented, not formalized)

- **Theorem 2.1** (`Ω(k·n^{1/k})` / `Ω(log n / log(k/log n))` regimes): requires a
  formalized Ramsey–type bound `R(k+1, l+1)`; currently not in Mathlib. Thm 2.2
  already gives the optimal-order bound for the headline parameters.
- **Theorems 2.3, 2.4** (upper-bound constructions): they assert existence of
  graphs via the probabilistic method on `G(n,p)` with concentration estimates and
  `o(1)`/`a.s.` reasoning — a substantially larger formalization effort. The
  catalog question ("how large an independent set *must* the whole graph have") is
  the lower-bound direction.
- The Erdős–Hajnal Ramsey-type conjecture of Section 4 (still open).

## Dependencies

- Lean `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0` only.
- No custom axioms; the build must reduce to the three standard axioms.
