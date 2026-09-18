# JSP-000661 — Locally large independent sets force a large global one

**Catalog entry**: [JSP-000661](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#jsp-000661)
**Source**: N. Alon, B. Sudakov, *On graphs with subgraphs having large independence numbers*,
J. Graph Theory 56 (2007), 149–157. arXiv:0706.4099.

## Problem (as stated in the catalog)

若图的每个 k-局部子图都有大独立集，整体独立集至少多大？
(*If every local part of a graph has a large independent set, how large an independent set
must the whole graph have?*)

## Exact quantitative form (from the paper)

For `n > s > t` define

> **f(n, s, t)** = the largest integer `f` such that every graph `G` on `n` vertices
> in which every induced subgraph on `s` vertices has an independent set of size `t`
> satisfies `α(G) ≥ f`.

Motivating instance (Erdős–Hajnal): `s = log³ n`, `t = log n`. The paper proves

> **q(n) = Θ(log² n / log log n).**

### Theorems of the paper (verbatim statements)

- **Theorem 2.1** (lower bound). Let `t < s < n/2`, and let `G` be a graph of order `n`
  such that every induced subgraph of `G` on `s` vertices contains an independent set of
  size `t`. Denote `k = ⌊s/(t−1)⌋`. Then `G` contains an independent set of size at
  least `Ω(k·n^{1/k})` if `k ≤ 2 log n`, and of size at least
  `Ω(log n / log(k/log n))` if `k > 2 log n`.

- **Theorem 2.2** (lower bound — headline). Let `2t ≤ s < n/2`, and let `G` be a graph
  of order `n` such that every induced subgraph of `G` on `s` vertices contains an
  independent set of size `t`. Then `G` contains an independent set of size at least
  `Ω( t·log(n/s) / log(s/t) )`.

- **Theorem 2.3** (upper bound construction). For every sufficiently large `t` and
  `2t ≤ s ≤ n/2` there exists a graph `G` on `n` vertices with
  `α(G) ≤ O( t·(n/s)^{2t/(s−t)}·log(n/t) )`
  such that every induced subgraph of `G` of order `s` contains an independent set of
  size `t`.

- **Theorem 2.4** (upper bound construction, improved range). Let `t < s ≤ n/2` with
  `s ≤ e^{2t}`, and assume either `(s/t)^{1−δ} ≥ log n` for some constant `δ > 0`,
  or `s/t = Ω(log n)` and `log t ≥ log^γ n` for some constant `γ > 0`. Then there is a
  graph `G` on `n` vertices with `α(G) ≤ O( t·log(n/t)/log(s/t) )` such that every
  induced subgraph of order `s` contains an independent set of size `t`.

## Formalized headline statement

The Lean development proves a fully explicit (no asymptotic notation) form of
Theorem 2.2's content. Writing `b = ⌊t/2⌋`, the proof in the paper iterates a
deterministic peeling step `I` times while the residual set has ≥ `s` vertices, each
round contributing `b` vertices to a global independent set. Quantifying the iteration
bound gives the headline theorem:

```lean
theorem indepNumber_of_locally_large {n s t : ℕ}
    (ht : 2 ≤ t) (hst : 2 * t ≤ s) (hsn : 2 * s < n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hlocal : ∀ U : Finset (Fin n), U.card = s →
      ∃ J ⊆ U, J.card = t ∧ G.IsIndepSet J)
    (I : ℕ) (hI : s ^ (2 * I - 1) ≤ n) :
    ∃ J : Finset (Fin n), J.card ≥ (t / 2) * I ∧ G.IsIndepSet J
```

For the Erdős–Hajnal parameters `s = Θ(log³ n)`, `t = Θ(log n)` one may take
`I = Θ(log n / log log n)`, recovering `α(G) ≥ Ω(log² n / log log n)` — the same order
as the paper's lower bound for `q(n)`. See `SCOPE.md` for what is and is not
formalized.
