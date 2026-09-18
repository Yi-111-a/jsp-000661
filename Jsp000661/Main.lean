import Jsp000661.Counting

/-!
# Main theorem for JSP-000661

Alon–Sudakov, *On graphs with subgraphs having large independence numbers*
(J. Graph Theory 2007), Theorem 2.2 direction, in explicit integer form:

if every `s`-vertex subset contains an independent `t`-set, then for every `I`
with `s·(36s²)^(I−1) ≤ n·t^(2(I−1))` the graph has an independent set of size
`≥ (t/2)·I`.  This matches the paper's decay factor `t²/(4e²s²)` up to the
integer `e`-proxy `3` (`4e² ≈ 29.6 ≤ 36`).

The proof iterates `peel_step`: at round `i` we have an independent set `J` of
size `(t/2)·i` and a residual `W` with `n·t^(2i) ≤ |W|·(36s²)^i` and no `J`–`W`
edges; we peel a new `(t/2)`-set `X` out of `W` and continue inside `W' ⊆ W ∖ X`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Iteration invariant: after `i` rounds there is an independent set `J` of size
`(t/2)·i` and a residual `W` with no `J`–`W` edges and
`|V|·t^(2i) ≤ |W|·(36s²)^i`. -/
theorem iter_aux (s t : ℕ) (ht : 2 ≤ t) (hst : 2 * t ≤ s)
    (hloc : G.LocallyLargeIndep s t)
    (I : ℕ) (hI : s * (36 * s ^ 2) ^ (I - 1) ≤ Fintype.card V * t ^ (2 * (I - 1))) :
    ∀ i : ℕ, i ≤ I →
      ∃ J W : Finset V, G.IsIndepSet J ∧ J.card = (t / 2) * i ∧
        Disjoint J W ∧ (∀ x ∈ J, ∀ y ∈ W, ¬ G.Adj x y) ∧
        Fintype.card V * t ^ (2 * i) ≤ W.card * (36 * s ^ 2) ^ i := by
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
    -- the residual still has ≥ s vertices: `s·(36s²)^i ≤ n·t^{2i} ≤ |W|·(36s²)^i`.
    have hWs : s ≤ W.card := by
      have hs0 : 0 < s := by omega
      have hK : 0 < 36 * s ^ 2 := Nat.mul_pos (by omega) (Nat.pow_pos hs0)
      have htsq : t ^ 2 ≤ 36 * s ^ 2 :=
        le_trans (Nat.pow_le_pow_left (by omega : t ≤ s) 2)
          (le_mul_of_one_le_left' (by omega : (1 : ℕ) ≤ 36))
      have key : s * (36 * s ^ 2) ^ i * (36 * s ^ 2) ^ (I - 1 - i)
          ≤ Fintype.card V * t ^ (2 * i) * (36 * s ^ 2) ^ (I - 1 - i) := by
        calc s * (36 * s ^ 2) ^ i * (36 * s ^ 2) ^ (I - 1 - i)
            = s * (36 * s ^ 2) ^ (I - 1) := by
              rw [mul_assoc, ← pow_add]; congr 1; congr 1; omega
          _ ≤ Fintype.card V * t ^ (2 * (I - 1)) := hI
          _ = Fintype.card V * t ^ (2 * i) * t ^ (2 * (I - 1 - i)) := by
              rw [mul_assoc, ← pow_add]; congr 1; congr 1; omega
          _ ≤ Fintype.card V * t ^ (2 * i) * (36 * s ^ 2) ^ (I - 1 - i) := by
              apply Nat.mul_le_mul_left
              rw [pow_mul]
              exact Nat.pow_le_pow_left htsq _
      have hres : s * (36 * s ^ 2) ^ i ≤ Fintype.card V * t ^ (2 * i) :=
        Nat.le_of_mul_le_mul_right key (Nat.pow_pos hK)
      have h1 : s * (36 * s ^ 2) ^ i ≤ W.card * (36 * s ^ 2) ^ i := hres.trans hWi
      exact Nat.le_of_mul_le_mul_right h1 (Nat.pow_pos hK)
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
    · calc Fintype.card V * t ^ (2 * (i + 1))
          = (Fintype.card V * t ^ (2 * i)) * t ^ 2 := by
            rw [show 2 * (i + 1) = 2 * i + 2 from by omega, pow_add]; ring
        _ ≤ (W.card * (36 * s ^ 2) ^ i) * t ^ 2 := Nat.mul_le_mul hWi le_rfl
        _ = (W.card * t ^ 2) * (36 * s ^ 2) ^ i := by ring
        _ ≤ (W'.card * (36 * s ^ 2)) * (36 * s ^ 2) ^ i :=
            Nat.mul_le_mul hdec le_rfl
        _ = W'.card * (36 * s ^ 2) ^ (i + 1) := by rw [pow_succ']; ring

/-- **Alon–Sudakov, Theorem 2.2 direction.**  If every `s`-vertex subset of an
`n`-vertex graph contains an independent set of size `t`, then for every `I`
with `s·(36s²)^(I−1) ≤ n·t^(2(I−1))` the graph has independence number
`≥ (t/2)·I`. -/
theorem indepNumber_of_locally_large {n s t : ℕ}
    (ht : 2 ≤ t) (hst : 2 * t ≤ s)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hlocal : G.LocallyLargeIndep s t)
    (I : ℕ) (hI : s * (36 * s ^ 2) ^ (I - 1) ≤ n * t ^ (2 * (I - 1))) :
    (t / 2) * I ≤ G.indepNum := by
  have hI' : s * (36 * s ^ 2) ^ (I - 1)
      ≤ Fintype.card (Fin n) * t ^ (2 * (I - 1)) := by
    rw [Fintype.card_fin]; exact hI
  obtain ⟨J, _, hJi, hJc, -, -, -⟩ :=
    iter_aux s t ht hst hlocal I hI' I le_rfl
  rw [← hJc]
  exact hJi.card_le_indepNum

end SimpleGraph
