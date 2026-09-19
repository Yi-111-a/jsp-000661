# Claim record for JSP-000661 (submitted 2026-09-19 with owner approval)

Submitted:

- Catalog correction PR: https://github.com/TheJustinSunPrize/awards/pull/1630
- Award claim issue: https://github.com/TheJustinSunPrize/awards/issues/1631

Both are pending maintainer review; submission does not imply acceptance or
award confirmation.

Award claim form fields (see awards/CONTRIBUTING.md):

## Problem-bank link
https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000661

## Original Lean proof repository
https://github.com/Yi-111-a/jsp-000661

- Pinned commit (40-char SHA): `37fafb7f2e925db577551515140f74bacc4a469c`
- Toolchain: `leanprover/lean4:v4.34.0` (Mathlib v4.34.0)
- Headline theorem: `SimpleGraph.indepNumber_of_locally_large`
  (`Jsp000661/Main.lean`)
- Harness evidence: `HARNESS_LOG.md` in the same commit —
  `lake build` green, 0 `sorry`/`admit`,
  axioms = `[propext, Classical.choice, Quot.sound]` only.

## What is formalized
Alon–Sudakov, *On graphs with subgraphs having large independence numbers*
(J. Graph Theory 55 (2007), 149–157), Theorem 2.2 direction, in explicit
integer form:

> For a finite simple graph `G` on `n` vertices, if every `s`-vertex subset
> contains an independent set of size `t` (with `2 ≤ t`, `2t ≤ s`), then for
> every natural `I` satisfying `s·(36s²)^(I−1) ≤ n·t^(2(I−1))`, `G` has
> independence number `≥ (t/2) · I`.

The iteration keeps the paper's `t²/(4e²s²)` per-round decay factor (integer
`e`-proxy `3`, giving the explicit constant `36`), so the bound matches
Theorem 2.2's `t·log(n/s)/log(s²/t²)` shape in all parameter regimes. In the
Erdős–Hajnal regime `s = log³n`, `t = log n` this yields the
`Θ(log²n / log log n)` scale of the paper's `q(n)`. The probabilistic
upper-bound constructions (Theorems 2.3, 2.4) are documented as out of
scope in `SCOPE.md`.

## Contribution role
Lean formalization (definitions, double-counting lemmas, iteration proof,
build harness). Repository owner `Yi-111-a` matches the submitting GitHub
account.

## Follow-up contact email
2352737128@qq.com

## Identity verification method
Repository-owner/GitHub-account match per CONTRIBUTING.md (submitting account
`Yi-111-a` owns the proof repository `Yi-111-a/jsp-000661`).
