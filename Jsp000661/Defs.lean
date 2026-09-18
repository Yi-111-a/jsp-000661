import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Powerset

/-!
# Definitions for JSP-000661

The local condition "every `s`-vertex induced subgraph has an independent set of
size `t`", stated in terms of `Finset`s of vertices.  We use Mathlib's
`SimpleGraph.IsIndepSet` / `SimpleGraph.indepNum` throughout.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The hypothesis of the Alon–Sudakov theorem: every `s`-vertex subset `U` of the
vertex set contains an independent set of size `t`. -/
def LocallyLargeIndep (s t : ℕ) : Prop :=
  ∀ U : Finset V, U.card = s → ∃ J : Finset V, J ⊆ U ∧ J.card = t ∧ G.IsIndepSet J

/-- Restricted version on a finset `W`: every `s`-subset of `W` contains an
independent `t`-set.  Holds inside any `W` when `G` is `LocallyLargeIndep`. -/
def LocallyLargeIndepOn (W : Finset V) (s t : ℕ) : Prop :=
  ∀ U : Finset V, U ⊆ W → U.card = s → ∃ J : Finset V, J ⊆ U ∧ J.card = t ∧ G.IsIndepSet J

theorem LocallyLargeIndep.on {s t : ℕ} (h : G.LocallyLargeIndep s t) (W : Finset V) :
    G.LocallyLargeIndepOn W s t := fun U _ hU => h U hU

theorem IsIndepSet.subset' {G : SimpleGraph V} {I J : Finset V}
    (hI : G.IsIndepSet I) (hJI : J ⊆ I) : G.IsIndepSet J :=
  Set.Pairwise.mono (Finset.coe_subset.mpr hJI) hI

end SimpleGraph
