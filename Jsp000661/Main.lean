import Jsp000661.Counting

/-!
# Main theorem for JSP-000661

Alon–Sudakov, *On graphs with subgraphs having large independence numbers*
(J. Graph Theory 2007), Theorem 2.2 direction, in explicit integer form:

if every `s`-vertex subset contains an independent `t`-set, then for every `I`
with `s^(2I−1) ≤ n` the graph has an independent set of size `≥ (t/2)·I`.

The proof iterates `peel_step`: at round `i` we have an independent set `J` of
size `(t/2)·i` and a residual `W` with `n ≤ |W|·s^(2i)` and no `J`–`W` edges;
we peel a new `(t/2)`-set `X` out of `W` and continue inside `W' ⊆ W ∖ X`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Iteration invariant: after `i` rounds there is an independent set `J` of size
`(t/2)·i` and a residual `W` with no `J`–`W` edges and `|V| ≤ |W|·s^(2i)`. -/
theorem iter_aux (s t : ℕ) (ht : 2 ≤ t) (hst : 2 * t ≤ s)
    (hloc : G.LocallyLargeIndep s t)
    (I : ℕ) (hI : s ^ (2 * I - 1) ≤ Fintype.card V) :
    ∀ i : ℕ, i ≤ I →
      ∃ J W : Finset V, G.IsIndepSet J ∧ J.card = (t / 2) * i ∧
        Disjoint J W ∧ (∀ x ∈ J, ∀ y ∈ W, ¬ G.Adj x y) ∧
        Fintype.card V ≤ W.card * s ^ (2 * i) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨∅, univ, ?_, rfl, ?_, ?_, ?_⟩
    · simp [IsIndepSet]
    · exact disjoint_empty_left _
    · intro x hx; simp at hx
    · simp
  | succ i ih =>
    intro hi
    obtain ⟨J, W, hJi, hJc, hdJW, hJe, hWi⟩ := ih (Nat.le_of_succ_le hi)
    -- the residual still has ≥ s vertices: `s^(2i)·|W| ≥ s^(2I−1)`.
    have hWs : s ≤ W.card := by
      have h1 : s ^ (2 * I - 1) ≤ W.card * s ^ (2 * i) := hI.trans hWi
      have h2 : s ^ (2 * I - 1) = s ^ (2 * I - 1 - 2 * i) * s ^ (2 * i) := by
        rw [← pow_add]; congr 1; omega
      rw [h2] at h1
      have h4 : s ^ (2 * I - 1 - 2 * i) ≤ W.card :=
        Nat.le_of_mul_le_mul_right h1 (Nat.pow_pos (show 0 < s by omega))
      have h3 : s ≤ s ^ (2 * I - 1 - 2 * i) := by
        have hexp : 1 ≤ 2 * I - 1 - 2 * i := by omega
        calc s = s ^ 1 := (pow_one s).symm
          _ ≤ s ^ (2 * I - 1 - 2 * i) :=
              Nat.pow_le_pow_right (show 1 ≤ s by omega) hexp
      exact h3.trans h4
    obtain ⟨X, W', hXW, hW'W, hdXW', hXc, hXi, hno, hdec⟩ :=
      peel_step ht hst hWs (hloc.on W)
    refine ⟨J ∪ X, W', ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha b hb hab
      simp only [coe_union, Set.mem_union, mem_coe] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact hJi ha hb hab
      · exact hJe a ha b (hXW hb)
      · intro hAdj
        exact hJe b hb a (hXW ha) (G.adj_symm hAdj)
      · exact hXi ha hb hab
    · have hdJX : Disjoint J X := by
        rw [Finset.disjoint_left] at hdJW ⊢
        intro x hxJ hxX
        exact hdJW hxJ (hXW hxX)
      rw [card_union_of_disjoint hdJX, hJc, hXc]
      ring
    · have hJW' : Disjoint J W' := by
        rw [Finset.disjoint_left] at hdJW ⊢
        intro y hyJ hyW'
        exact hdJW hyJ (hW'W hyW')
      rw [Finset.disjoint_union_left]
      exact ⟨hJW', hdXW'⟩
    · intro x hx y hy
      rcases mem_union.mp hx with hxJ | hxX
      · exact hJe x hxJ y (hW'W hy)
      · exact hno x hxX y hy
    · calc Fintype.card V ≤ W.card * s ^ (2 * i) := hWi
        _ ≤ (W'.card * s ^ 2) * s ^ (2 * i) := Nat.mul_le_mul hdec le_rfl
        _ = W'.card * s ^ (2 * (i + 1)) := by
            rw [mul_assoc, ← pow_add, show 2 + 2 * i = 2 * (i + 1) from by omega]

/-- **Alon–Sudakov, Theorem 2.2 direction.**  If every `s`-vertex subset of an
`n`-vertex graph contains an independent set of size `t`, then for every `I`
with `s^(2I−1) ≤ n` the graph has independence number `≥ (t/2)·I`. -/
theorem indepNumber_of_locally_large {n s t : ℕ}
    (ht : 2 ≤ t) (hst : 2 * t ≤ s)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hlocal : G.LocallyLargeIndep s t)
    (I : ℕ) (hI : s ^ (2 * I - 1) ≤ n) :
    (t / 2) * I ≤ G.indepNum := by
  have hI' : s ^ (2 * I - 1) ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin]; exact hI
  obtain ⟨J, _, hJi, hJc, -, -, -⟩ :=
    iter_aux s t ht hst hlocal I hI' I le_rfl
  rw [← hJc]
  exact hJi.card_le_indepNum

end SimpleGraph
