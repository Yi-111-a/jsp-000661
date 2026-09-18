import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Definitions for JSP-000661

Independence number of a finite simple graph and the local condition
"every `s`-vertex induced subgraph has an independent set of size `t`".
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A finite set of vertices is independent if no two of its members are adjacent. -/
def IsIndependent (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ G.Adj x y

/-- The independence number `α(G)` on a finite vertex set:
the largest cardinality of an independent `Finset`. -/
noncomputable def indepNum [Fintype V] : ℕ :=
  (univ.powerset.filter (G.IsIndependent)).sup Finset.card

/-- `G.indepNum ≥ m` iff there is an independent set of size at least `m`. -/
theorem exists_independent_of_le_indepNum [Fintype V] {m : ℕ}
    (h : m ≤ G.indepNum) : ∃ s : Finset V, m ≤ s.card ∧ G.IsIndependent s := by
  sorry

theorem indepNum_le_of_forall [Fintype V] {m : ℕ}
    (h : ∀ s : Finset V, G.IsIndependent s → s.card ≤ m) : G.indepNum ≤ m := by
  sorry

end SimpleGraph
