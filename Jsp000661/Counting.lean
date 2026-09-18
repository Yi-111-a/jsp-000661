import Jsp000661.Defs
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# Counting lemmas for JSP-000661

The heart of Alon–Sudakov Theorem 2.2, in fully explicit integer form.

* `indepSets_card_lower`: double counting —
  `C(|W|,s) ≤ N · C(|W|−t, s−t)` where `N` is the number of independent
  `t`-subsets of `W`.
* `choose_pow_mul_le`: `m^t · C(s,t) ≤ s^t · C(m,t)` for `s ≤ m`
  (the product form of `C(m,t)/C(s,t) ≥ (m/s)^t`).
* `peel_step`: the iteration step — from `W` with `|W| ≥ s` extract an
  independent `X` of size `t/2` and a residual `W' ⊆ W ∖ X` with no edges to `X`
  and `|W| ≤ s² · |W'|`.
-/

open Finset
open scoped Classical

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Finset version of `G.IsIndepSet`, used as a filter predicate. -/
def indepPred (I : Finset V) : Prop := G.IsIndepSet (I : Set V)

/-! ### Double counting -/

/-- If every `s`-subset of `W` contains an independent `t`-set, then the number
of independent `t`-subsets of `W`, times `C(|W|−t, s−t)`, is at least
`C(|W|, s)`. -/
theorem indepSets_card_lower {W : Finset V} {s t : ℕ} (hts : t ≤ s)
    (hW : G.LocallyLargeIndepOn W s t) :
    Nat.choose W.card s ≤
      ((W.powersetCard t).filter G.indepPred).card *
        Nat.choose (W.card - t) (s - t) := by
  classical
  set 𝒰 := W.powersetCard s
  set 𝒩 := (W.powersetCard t).filter G.indepPred
  have hU : ∀ U ∈ 𝒰, ∃ J ∈ 𝒩, J ⊆ U := by
    intro U hU
    obtain ⟨hUW, hUs⟩ := mem_powersetCard.mp hU
    obtain ⟨J, hJU, hJt, hJin⟩ := hW U hUW hUs
    exact ⟨J, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hJU.trans hUW, hJt⟩, hJin⟩, hJU⟩
  have h1 : 𝒰.card ≤ ∑ U ∈ 𝒰, (𝒩.filter (· ⊆ U)).card := by
    rw [card_eq_sum_ones]
    apply sum_le_sum
    intro U hUmem
    obtain ⟨J, hJ, hJU⟩ := hU U hUmem
    have : (𝒩.filter (· ⊆ U)).Nonempty := ⟨J, mem_filter.mpr ⟨hJ, hJU⟩⟩
    exact Nat.succ_le_of_lt (card_pos.mpr this)
  have h2 : ∑ U ∈ 𝒰, (𝒩.filter (· ⊆ U)).card
      = ∑ I ∈ 𝒩, (𝒰.filter (I ⊆ ·)).card := by
    simp_rw [card_filter]
    exact sum_comm
  have h3 : ∀ I ∈ 𝒩, (𝒰.filter (I ⊆ ·)).card = Nat.choose (W.card - t) (s - t) := by
    intro I hI
    have hIW : I ⊆ W := (mem_powersetCard.mp (mem_filter.mp hI).1).1
    have hIt : I.card = t := (mem_powersetCard.mp (mem_filter.mp hI).1).2
    rw [card_filter_powersetCard_subset I W s hIW (hIt ▸ hts), hIt]
  rw [h2, sum_congr rfl h3, sum_const, smul_eq_mul, card_powersetCard] at h1
  exact h1

/-! ### Binomial ratio bound -/

private lemma mul_sub_le_mul_sub {m s t : ℕ} (hsm : s ≤ m) :
    m * (s - t) ≤ s * (m - t) := by
  by_cases hts : t ≤ s
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsm
    rw [show s + d - t = s - t + d from by omega, add_mul, mul_add]
    apply Nat.add_le_add_left
    calc d * (s - t) ≤ d * s := Nat.mul_le_mul le_rfl (Nat.sub_le s t)
      _ = s * d := Nat.mul_comm _ _
  · rw [Nat.sub_eq_zero_of_le (le_of_lt (Nat.lt_of_not_ge hts)), mul_zero]
    exact Nat.zero_le _

/-- `m^t · s.descFactorial t ≤ s^t · m.descFactorial t` for `s ≤ m`:
each factor `m·(s−i) ≤ s·(m−i)` of the products contributes. -/
theorem descFactorial_mul_pow_le {m s : ℕ} (hsm : s ≤ m) (t : ℕ) :
    m ^ t * s.descFactorial t ≤ s ^ t * m.descFactorial t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, pow_succ, Nat.descFactorial_succ, Nat.descFactorial_succ]
    have hmul : m * (s - t) ≤ s * (m - t) := mul_sub_le_mul_sub hsm
    calc m ^ t * m * ((s - t) * s.descFactorial t)
        = (m ^ t * s.descFactorial t) * (m * (s - t)) := by ring
      _ ≤ (s ^ t * m.descFactorial t) * (s * (m - t)) := Nat.mul_le_mul ih hmul
      _ = s ^ t * s * ((m - t) * m.descFactorial t) := by ring

/-- Product form of `C(m,t)/C(s,t) ≥ (m/s)^t` for `s ≤ m`. -/
theorem choose_pow_mul_le {m s t : ℕ} (hsm : s ≤ m) :
    m ^ t * Nat.choose s t ≤ s ^ t * Nat.choose m t := by
  have h := descFactorial_mul_pow_le hsm t
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at h
  have h' : t.factorial * (m ^ t * Nat.choose s t) ≤
      t.factorial * (s ^ t * Nat.choose m t) := by
    calc t.factorial * (m ^ t * Nat.choose s t)
        = m ^ t * (t.factorial * Nat.choose s t) := by ring
      _ ≤ s ^ t * (t.factorial * Nat.choose m t) := h
      _ = t.factorial * (s ^ t * Nat.choose m t) := by ring
  exact Nat.le_of_mul_le_mul_left h' (Nat.factorial_pos t)

/-! ### The peeling step -/

/-- **Peeling step.**  If `|W| ≥ s` and every `s`-subset of `W` contains an
independent `t`-set, there is an independent `X ⊆ W` of size `t/2` and a set
`W' ⊆ W` disjoint from `X` with no `X`–`W'` edges and `|W| ≤ s²·|W'|`. -/
theorem peel_step {W : Finset V} {s t : ℕ}
    (ht : 2 ≤ t) (hst : 2 * t ≤ s) (hW : s ≤ W.card)
    (hloc : G.LocallyLargeIndepOn W s t) :
    ∃ X W' : Finset V, X ⊆ W ∧ W' ⊆ W ∧ Disjoint X W' ∧ X.card = t / 2 ∧
      G.IsIndepSet X ∧ (∀ x ∈ X, ∀ y ∈ W', ¬ G.Adj x y) ∧
      W.card ≤ W'.card * s ^ 2 := by
  classical
  set b := t / 2
  set r := t - t / 2
  set m := W.card
  have hts : t ≤ s := by omega
  have hbr : b + r = t := by omega
  have hb1 : 1 ≤ b := by omega
  have hr1 : 1 ≤ r := by omega
  have hr2 : t ≤ 2 * r := by omega
  have hbt : b ≤ t := by omega
  have hbm : b ≤ m := by omega
  have htm : t ≤ m := by omega
  have hm : 0 < m := by omega
  have hs : 0 < s := by omega
  set 𝒩 := (W.powersetCard t).filter G.indepPred
  -- (1) `N·C(s,t) ≥ C(m,t)` from the double count and `choose_mul`.
  have hN : Nat.choose m t ≤ 𝒩.card * Nat.choose s t := by
    have hA := indepSets_card_lower hts hloc
    have key : Nat.choose m t * Nat.choose (m - t) (s - t)
        ≤ (𝒩.card * Nat.choose s t) * Nat.choose (m - t) (s - t) := by
      calc Nat.choose m t * Nat.choose (m - t) (s - t)
          = Nat.choose m s * Nat.choose s t := (Nat.choose_mul hts).symm
        _ ≤ 𝒩.card * Nat.choose (m - t) (s - t) * Nat.choose s t :=
            Nat.mul_le_mul hA le_rfl
        _ = (𝒩.card * Nat.choose s t) * Nat.choose (m - t) (s - t) := by ring
    have hpos : 0 < Nat.choose (m - t) (s - t) :=
      Nat.pos_of_ne_zero (Nat.choose_ne_zero (Nat.sub_le_sub_right hW t))
    exact Nat.le_of_mul_le_mul_right key hpos
  -- (2) double count pairs `(X, I)` with `X ⊆ I`, `|X| = b`, `I ∈ 𝒩`:
  -- `∑_X c(X) = N·C(t,b)` where `c(X)` counts independent `t`-sets containing `X`.
  have hsum : ∑ X ∈ W.powersetCard b, (𝒩.filter (X ⊆ ·)).card
      = 𝒩.card * Nat.choose t b := by
    rw [sum_congr rfl (fun X _ => card_filter _ _), sum_comm]
    have inner : ∀ I ∈ 𝒩,
        ∑ X ∈ W.powersetCard b, ite (X ⊆ I) 1 0 = Nat.choose t b := by
      intro I hI
      rw [← card_filter]
      have hIW : I ⊆ W := (mem_powersetCard.mp (mem_filter.mp hI).1).1
      have hIt : I.card = t := (mem_powersetCard.mp (mem_filter.mp hI).1).2
      have heq : (W.powersetCard b).filter (· ⊆ I) = I.powersetCard b := by
        ext X
        simp only [mem_filter, mem_powersetCard]
        constructor
        · rintro ⟨⟨hXW, hXb⟩, hXI⟩; exact ⟨hXI, hXb⟩
        · rintro ⟨hXI, hXb⟩; exact ⟨⟨hXI.trans hIW, hXb⟩, hXI⟩
      rw [heq, card_powersetCard, hIt]
    rw [sum_congr rfl inner, sum_const, smul_eq_mul]
  -- (3) pigeonhole: some `X` lies in `≥ N·C(t,b)/C(m,b)` independent `t`-sets.
  have hpc : (W.powersetCard b).Nonempty := powersetCard_nonempty.mpr hbm
  have e12 : ∑ X ∈ W.powersetCard b, 𝒩.card * Nat.choose t b
      ≤ ∑ X ∈ W.powersetCard b, (𝒩.filter (X ⊆ ·)).card * Nat.choose m b := by
    have e1 : ∑ X ∈ W.powersetCard b, 𝒩.card * Nat.choose t b
        = Nat.choose m b * (𝒩.card * Nat.choose t b) := by
      rw [sum_const, smul_eq_mul, card_powersetCard]
    have e2 : ∑ X ∈ W.powersetCard b, (𝒩.filter (X ⊆ ·)).card * Nat.choose m b
        = Nat.choose m b * (𝒩.card * Nat.choose t b) := by
      rw [← Finset.sum_mul, hsum]; ring
    rw [e1, e2]
  obtain ⟨X, hX, hXc⟩ := Finset.exists_le_of_sum_le hpc e12
  obtain ⟨hXW, hXb⟩ := mem_powersetCard.mp hX
  -- (4) `X` is independent: it is contained in at least one `I ∈ 𝒩`.
  have hcX : 1 ≤ (𝒩.filter (X ⊆ ·)).card := by
    have hN1 : 1 ≤ 𝒩.card := by
      have h1 : 1 ≤ Nat.choose m t := Nat.pos_of_ne_zero (Nat.choose_ne_zero htm)
      have h3 : 1 ≤ 𝒩.card * Nat.choose s t := le_trans h1 hN
      rcases Nat.eq_zero_or_pos 𝒩.card with h0 | h0
      · rw [h0, zero_mul] at h3; omega
      · exact h0
    have hge : 1 ≤ (𝒩.filter (X ⊆ ·)).card * Nat.choose m b := by
      calc 1 ≤ 𝒩.card * Nat.choose t b :=
            Nat.mul_le_mul hN1 (Nat.pos_of_ne_zero (Nat.choose_ne_zero hbt))
        _ ≤ (𝒩.filter (X ⊆ ·)).card * Nat.choose m b := hXc
    rcases Nat.eq_zero_or_pos ((𝒩.filter (X ⊆ ·)).card) with h0 | h0
    · rw [h0, zero_mul] at hge; omega
    · exact h0
  have hXi : G.IsIndepSet X := by
    obtain ⟨I, hI⟩ := card_pos.mp hcX
    have hI𝒩 : I ∈ 𝒩 := (mem_filter.mp hI).1
    have hXI : X ⊆ I := (mem_filter.mp hI).2
    exact ((mem_filter.mp hI𝒩).2).subset' hXI
  -- (5) the residual `W'` = union of the `r`-complements of `X` in its extensions.
  set ℐ := 𝒩.filter (X ⊆ ·)
  set W' := ℐ.biUnion (· \ X)
  refine ⟨X, W', hXW, ?_, ?_, hXb, hXi, ?_, ?_⟩
  · intro y hy
    obtain ⟨I, hI, hy⟩ := mem_biUnion.mp hy
    have hIW : I ⊆ W := (mem_powersetCard.mp (mem_filter.mp (mem_filter.mp hI).1).1).1
    exact hIW (mem_sdiff.mp hy).1
  · rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨I, hI, hy⟩ := mem_biUnion.mp hy
    exact (mem_sdiff.mp hy).2 hx
  · intro x hx y hy hxy
    obtain ⟨I, hI, hyI⟩ := mem_biUnion.mp hy
    have hIi : G.IsIndepSet I := (mem_filter.mp (mem_filter.mp hI).1).2
    have hXI : X ⊆ I := (mem_filter.mp hI).2
    have hyI' : y ∈ I := (mem_sdiff.mp hyI).1
    exact hIi (hXI hx) hyI' (fun h => (mem_sdiff.mp hyI).2 (h ▸ hx)) hxy
  -- (6) cardinalities: `ℐ.card ≤ |W'|^r`, then the final `m ≤ s²·|W'|`.
  · have hcard : ℐ.card ≤ W'.card ^ r := by
      have hinj : Set.InjOn (· \ X) ℐ := by
        intro I₁ hI₁ I₂ hI₂ h
        have hXI₁ : X ⊆ I₁ := (mem_filter.mp (mem_coe.mp hI₁)).2
        have hXI₂ : X ⊆ I₂ := (mem_filter.mp (mem_coe.mp hI₂)).2
        have h' : I₁ \ X = I₂ \ X := h
        calc I₁ = X ∪ (I₁ \ X) := (union_sdiff_of_subset hXI₁).symm
          _ = X ∪ (I₂ \ X) := by rw [h']
          _ = I₂ := union_sdiff_of_subset hXI₂
      have hmaps : ∀ I ∈ ℐ, I \ X ∈ W'.powersetCard r := by
        intro I hI
        rw [mem_powersetCard]
        have hXI : X ⊆ I := (mem_filter.mp hI).2
        have hIt : I.card = t :=
          (mem_powersetCard.mp (mem_filter.mp (mem_filter.mp hI).1).1).2
        refine ⟨?_, ?_⟩
        · intro y hy; exact mem_biUnion.mpr ⟨I, hI, hy⟩
        · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hXI, hIt, hXb]
      have hle : ℐ.card ≤ (W'.powersetCard r).card :=
        card_le_card_of_injOn (· \ X) hmaps hinj
      rw [card_powersetCard] at hle
      exact hle.trans (Nat.choose_le_pow _ _)
    -- algebra: `m^r ≤ |W'|^r · s^t`, then take `r`-th roots.
    have key : m ^ r ≤ W'.card ^ r * s ^ t := by
      have e4 : m ^ t ≤ (𝒩.filter (X ⊆ ·)).card * Nat.choose m b * s ^ t := by
        have step1 : Nat.choose t b * (m ^ t * Nat.choose s t)
            ≤ (𝒩.filter (X ⊆ ·)).card * Nat.choose m b * Nat.choose s t * s ^ t := by
          calc Nat.choose t b * (m ^ t * Nat.choose s t)
              ≤ Nat.choose t b * (s ^ t * Nat.choose m t) :=
                Nat.mul_le_mul le_rfl (choose_pow_mul_le hW)
            _ = s ^ t * Nat.choose t b * Nat.choose m t := by ring
            _ ≤ s ^ t * Nat.choose t b * (𝒩.card * Nat.choose s t) :=
                Nat.mul_le_mul le_rfl hN
            _ = s ^ t * Nat.choose s t * (𝒩.card * Nat.choose t b) := by ring
            _ ≤ s ^ t * Nat.choose s t *
                  ((𝒩.filter (X ⊆ ·)).card * Nat.choose m b) :=
                Nat.mul_le_mul le_rfl hXc
            _ = (𝒩.filter (X ⊆ ·)).card * Nat.choose m b * Nat.choose s t * s ^ t :=
                by ring
        have step2 : m ^ t * Nat.choose s t
            ≤ (𝒩.filter (X ⊆ ·)).card * Nat.choose m b * Nat.choose s t * s ^ t :=
          le_trans
            (le_mul_of_one_le_left (Nat.zero_le _)
              (Nat.pos_of_ne_zero (Nat.choose_ne_zero hbt)))
            step1
        have hpos_st : 0 < Nat.choose s t :=
          Nat.pos_of_ne_zero (Nat.choose_ne_zero hts)
        have step3 : (m ^ t) * Nat.choose s t
            ≤ ((𝒩.filter (X ⊆ ·)).card * Nat.choose m b * s ^ t) * Nat.choose s t := by
          calc (m ^ t) * Nat.choose s t
              ≤ (𝒩.filter (X ⊆ ·)).card * Nat.choose m b * Nat.choose s t * s ^ t :=
                step2
            _ = ((𝒩.filter (X ⊆ ·)).card * Nat.choose m b * s ^ t) * Nat.choose s t :=
                by ring
        exact Nat.le_of_mul_le_mul_right step3 hpos_st
      have e5 : m ^ r ≤ (𝒩.filter (X ⊆ ·)).card * s ^ t := by
        have hCmb : Nat.choose m b ≤ m ^ b := Nat.choose_le_pow m b
        have e6 : m ^ b * m ^ r
            ≤ (𝒩.filter (X ⊆ ·)).card * m ^ b * s ^ t := by
          calc m ^ b * m ^ r = m ^ (b + r) := (pow_add m b r).symm
            _ = m ^ t := by rw [hbr]
            _ ≤ (𝒩.filter (X ⊆ ·)).card * Nat.choose m b * s ^ t := e4
            _ ≤ (𝒩.filter (X ⊆ ·)).card * m ^ b * s ^ t :=
                Nat.mul_le_mul (Nat.mul_le_mul le_rfl hCmb) le_rfl
        rw [show (𝒩.filter (X ⊆ ·)).card * m ^ b * s ^ t
            = m ^ b * ((𝒩.filter (X ⊆ ·)).card * s ^ t) from by ring] at e6
        exact Nat.le_of_mul_le_mul_left e6 (Nat.pow_pos hm)
      calc m ^ r ≤ (𝒩.filter (X ⊆ ·)).card * s ^ t := e5
        _ ≤ W'.card ^ r * s ^ t := Nat.mul_le_mul hcard le_rfl
    have hroot : m ≤ W'.card * s ^ 2 := by
      have hpow : m ^ r ≤ (W'.card * s ^ 2) ^ r := by
        calc m ^ r ≤ W'.card ^ r * s ^ t := key
          _ ≤ W'.card ^ r * s ^ (2 * r) :=
              Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right hs hr2)
          _ = (W'.card * s ^ 2) ^ r := by
              rw [mul_pow, ← pow_mul]
      exact (Nat.pow_le_pow_iff_left (by omega : r ≠ 0)).mp hpow
    exact hroot

end SimpleGraph
