import Jsp000661.Defs
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Ring.GeomSum
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
  and `|W|·t² ≤ 36·s²·|W'|`. This is the paper's `t²/(4e²s²)` decay factor with
  `3` as an integer `e`-proxy, via the sharp binomial estimates
  `t^b ≤ b^b·C(t,b)` and `C(m,b)·b^b ≤ (3m)^b` (the latter through
  `b^b ≤ 3^b·b!`).
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

/-! ### Factorial bound `b^b ≤ 3^b · b!` -/

/-- `∏_{i < k} (n - i) = n.descFactorial k`. -/
theorem prod_range_sub_eq_descFactorial (n k : ℕ) :
    ∏ i ∈ Finset.range k, (n - i) = n.descFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ, mul_comm]

/-- `2^j ≤ (j+1)!`. -/
theorem two_pow_le_factorial_succ : ∀ j : ℕ, 2 ^ j ≤ (j + 1).factorial := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    calc 2 ^ (j + 1) = 2 * 2 ^ j := pow_succ' 2 j
      _ ≤ 2 * (j + 1).factorial := Nat.mul_le_mul le_rfl ih
      _ ≤ (j + 2) * (j + 1).factorial := Nat.mul_le_mul (by omega) le_rfl
      _ = (j + 2).factorial := (Nat.factorial_succ _).symm

/-- The `j`-th binomial term of `(b+1)^b` decays geometrically:
`C(b,j)·b^{b-j}·2^{j-1} ≤ b^b` for `1 ≤ j ≤ b`. -/
theorem choose_mul_pow_mul_two_pow_le {b j : ℕ} (hj : 1 ≤ j) (hjb : j ≤ b) :
    Nat.choose b j * b ^ (b - j) * 2 ^ (j - 1) ≤ b ^ b := by
  have hdesc : Nat.choose b j * j.factorial = b.descFactorial j := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
  have h2j : 2 ^ (j - 1) ≤ j.factorial := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [show 1 + j - 1 = j from by omega, show 1 + j = j + 1 from by omega]
    exact two_pow_le_factorial_succ j
  have key : Nat.choose b j * b ^ (b - j) * 2 ^ (j - 1) * j.factorial
      ≤ b ^ b * j.factorial := by
    calc Nat.choose b j * b ^ (b - j) * 2 ^ (j - 1) * j.factorial
        = (Nat.choose b j * j.factorial) * b ^ (b - j) * 2 ^ (j - 1) := by ring
      _ = b.descFactorial j * b ^ (b - j) * 2 ^ (j - 1) := by rw [hdesc]
      _ ≤ b ^ j * b ^ (b - j) * 2 ^ (j - 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.descFactorial_le_pow b j) le_rfl) le_rfl
      _ = b ^ b * 2 ^ (j - 1) := by
          rw [← pow_add, Nat.add_sub_cancel' hjb]
      _ ≤ b ^ b * j.factorial := Nat.mul_le_mul le_rfl h2j
  exact Nat.le_of_mul_le_mul_right key (Nat.factorial_pos j)

/-- `∑_{j<b} 2^j = 2^b − 1`. -/
theorem geom_sum_two (b : ℕ) : ∑ j ∈ Finset.range b, 2 ^ j = 2 ^ b - 1 := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih, pow_succ' _ _]
    omega

/-- `(b+1)^b ≤ 3·b^b`, the integer form of `(1+1/b)^b ≤ 3`. -/
theorem add_one_pow_le_three_mul_pow (b : ℕ) : (b + 1) ^ b ≤ 3 * b ^ b := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  have e : (b + 1) ^ b = ∑ k ∈ Finset.range (b + 1), Nat.choose b k * b ^ k := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro k _
    rw [one_pow, mul_one]
    exact Nat.mul_comm _ _
  rw [e]
  have reidx : ∑ k ∈ Finset.range (b + 1), Nat.choose b k * b ^ k
      = ∑ j ∈ Finset.range (b + 1), Nat.choose b j * b ^ (b - j) := by
    rw [← Finset.sum_range_reflect (fun k => Nat.choose b k * b ^ k) (b + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    have hkb : k ≤ b := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [show b + 1 - 1 - k = b - k from by omega, Nat.choose_symm hkb]
  rw [reidx, Finset.sum_range_succ']
  have h0 : Nat.choose b 0 * b ^ (b - 0) = b ^ b := by simp
  rw [h0]
  have hsum : ∑ j ∈ Finset.range b, Nat.choose b (j + 1) * b ^ (b - (j + 1))
      ≤ 2 * b ^ b := by
    have hw : ∀ j ∈ Finset.range b,
        Nat.choose b (j + 1) * b ^ (b - (j + 1)) * 2 ^ (b - 1)
          ≤ b ^ b * 2 ^ (b - 1 - j) := by
      intro j hj
      have hjb : j + 1 ≤ b := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
      have hmain := choose_mul_pow_mul_two_pow_le (b := b) (j := j + 1) (by omega) hjb
      calc Nat.choose b (j + 1) * b ^ (b - (j + 1)) * 2 ^ (b - 1)
          = (Nat.choose b (j + 1) * b ^ (b - (j + 1)) * 2 ^ ((j + 1) - 1))
              * 2 ^ (b - 1 - j) := by
            have e2 : (2 : ℕ) ^ (b - 1) = 2 ^ ((j + 1) - 1) * 2 ^ (b - 1 - j) := by
              rw [← pow_add]; congr 1; omega
            rw [e2]; ring
        _ ≤ b ^ b * 2 ^ (b - 1 - j) := Nat.mul_le_mul hmain le_rfl
    have hsumw : (∑ j ∈ Finset.range b, Nat.choose b (j + 1) * b ^ (b - (j + 1)))
          * 2 ^ (b - 1) ≤ (2 * b ^ b) * 2 ^ (b - 1) := by
      rw [Finset.sum_mul]
      calc ∑ j ∈ Finset.range b, Nat.choose b (j + 1) * b ^ (b - (j + 1)) * 2 ^ (b - 1)
          ≤ ∑ j ∈ Finset.range b, b ^ b * 2 ^ (b - 1 - j) := Finset.sum_le_sum hw
        _ = b ^ b * ∑ j ∈ Finset.range b, 2 ^ (b - 1 - j) := by rw [Finset.mul_sum]
        _ = b ^ b * ∑ j ∈ Finset.range b, 2 ^ j := by
            congr 1
            exact Finset.sum_range_reflect (fun j => 2 ^ j) b
        _ = b ^ b * (2 ^ b - 1) := by
            congr 1
            exact geom_sum_two b
        _ ≤ b ^ b * 2 ^ b := Nat.mul_le_mul le_rfl (Nat.sub_le _ _)
        _ = (2 * b ^ b) * 2 ^ (b - 1) := by
            have e2b : (2 : ℕ) ^ b = 2 * 2 ^ (b - 1) := by
              conv_lhs => rw [show b = b - 1 + 1 from by omega]
              rw [pow_succ']
            rw [e2b]; ring
    exact Nat.le_of_mul_le_mul_right hsumw (Nat.pow_pos (by omega : 0 < 2))
  calc ∑ j ∈ Finset.range b, Nat.choose b (j + 1) * b ^ (b - (j + 1)) + b ^ b
      ≤ 2 * b ^ b + b ^ b := Nat.add_le_add hsum le_rfl
    _ = 3 * b ^ b := by ring

/-- **Factorial lower bound**: `b^b ≤ 3^b · b!`. -/
theorem pow_le_three_pow_factorial (b : ℕ) : b ^ b ≤ 3 ^ b * b.factorial := by
  induction b with
  | zero => simp
  | succ b ih =>
    calc (b + 1) ^ (b + 1) = (b + 1) * (b + 1) ^ b := pow_succ' _ _
      _ ≤ (b + 1) * (3 * b ^ b) := Nat.mul_le_mul le_rfl (add_one_pow_le_three_mul_pow b)
      _ ≤ (b + 1) * (3 * (3 ^ b * b.factorial)) :=
          Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl ih)
      _ = 3 ^ (b + 1) * (b + 1).factorial := by
          rw [Nat.factorial_succ, pow_succ']; ring

/-- `t^b ≤ b^b · C(t,b)` for `b ≤ t`, the product form of `(t/b)^b ≤ C(t,b)`. -/
theorem pow_le_pow_mul_choose {t b : ℕ} (hbt : b ≤ t) :
    t ^ b ≤ b ^ b * Nat.choose t b := by
  classical
  have key : ∏ i ∈ Finset.range b, (t * (b - i)) ≤ ∏ i ∈ Finset.range b, (b * (t - i)) := by
    apply Finset.prod_le_prod
    intro i hi
    have hbi : i ≤ b := (Finset.mem_range.mp hi).le
    have hit : i ≤ t := hbi.trans hbt
    have e1 : t * (b - i) + t * i = t * b := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hbi]
    have e2 : b * (t - i) + b * i = b * t := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hit]
    calc t * (b - i) = t * b - t * i := by omega
      _ ≤ t * b - b * i := Nat.sub_le_sub_left (Nat.mul_le_mul hbt le_rfl) _
      _ = b * (t - i) := by
          have hcomm : t * b = b * t := Nat.mul_comm _ _
          omega
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_const, Finset.card_range] at key
  rw [prod_range_sub_eq_descFactorial, prod_range_sub_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.choose_self, mul_one] at key
  have h' : b.factorial * t ^ b ≤ b.factorial * (b ^ b * Nat.choose t b) := by
    calc b.factorial * t ^ b = t ^ b * b.factorial := by ring
      _ ≤ b ^ b * (b.factorial * Nat.choose t b) := key
      _ = b.factorial * (b ^ b * Nat.choose t b) := by ring
  exact Nat.le_of_mul_le_mul_left h' (Nat.factorial_pos b)

/-! ### The peeling step -/

/-- **Peeling step.**  If `|W| ≥ s` and every `s`-subset of `W` contains an
independent `t`-set, there is an independent `X ⊆ W` of size `t/2` and a set
`W' ⊆ W` disjoint from `X` with no `X`–`W'` edges and
`|W|·t² ≤ 36·s²·|W'|` — the paper's `t²/(4e²s²)` decay, `e`↦`3`. -/
theorem peel_step {W : Finset V} {s t : ℕ}
    (ht : 2 ≤ t) (hst : 2 * t ≤ s) (hW : s ≤ W.card)
    (hloc : G.LocallyLargeIndepOn W s t) :
    ∃ X W' : Finset V, X ⊆ W ∧ W' ⊆ W ∧ Disjoint X W' ∧ X.card = t / 2 ∧
      G.IsIndepSet X ∧ (∀ x ∈ X, ∀ y ∈ W', ¬ G.Adj x y) ∧
      W.card * t ^ 2 ≤ W'.card * (36 * s ^ 2) := by
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
  -- (6) cardinalities: `ℐ.card ≤ C(|W'|, r)`, then the sharper
  -- `m·t² ≤ 36·s²·|W'|` (paper's `t²/(4e²s²)` factor with `3` as an `e`-proxy).
  · have hchoose : ℐ.card ≤ Nat.choose W'.card r := by
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
      exact hle
    -- `N·s^t ≥ m^t` from the double count and the ratio bound.
    have hNst : m ^ t ≤ 𝒩.card * s ^ t := by
      have key2 : m ^ t * Nat.choose s t ≤ (𝒩.card * s ^ t) * Nat.choose s t := by
        calc m ^ t * Nat.choose s t ≤ s ^ t * Nat.choose m t := choose_pow_mul_le hW
          _ ≤ s ^ t * (𝒩.card * Nat.choose s t) := Nat.mul_le_mul le_rfl hN
          _ = (𝒩.card * s ^ t) * Nat.choose s t := by ring
      exact Nat.le_of_mul_le_mul_right key2 (Nat.pos_of_ne_zero (Nat.choose_ne_zero hts))
    -- `c·3^b·s^t ≥ m^r·t^b`, keeping the `C(t,b)/C(m,b)` ratio sharp.
    have hc : m ^ r * t ^ b ≤ ℐ.card * 3 ^ b * s ^ t := by
      have e1 : Nat.choose m b * b ^ b ≤ (3 * m) ^ b := by
        calc Nat.choose m b * b ^ b
            ≤ Nat.choose m b * (3 ^ b * b.factorial) :=
              Nat.mul_le_mul le_rfl (pow_le_three_pow_factorial b)
          _ = 3 ^ b * (b.factorial * Nat.choose m b) := by ring
          _ = 3 ^ b * m.descFactorial b := by
              rw [Nat.descFactorial_eq_factorial_mul_choose]
          _ ≤ 3 ^ b * m ^ b := Nat.mul_le_mul le_rfl (Nat.descFactorial_le_pow _ _)
          _ = (3 * m) ^ b := (mul_pow _ _ _).symm
      have e2 : m ^ b * (m ^ r * t ^ b) ≤ m ^ b * (ℐ.card * 3 ^ b * s ^ t) := by
        have hL1 : t ^ b ≤ b ^ b * Nat.choose t b := pow_le_pow_mul_choose hbt
        calc m ^ b * (m ^ r * t ^ b) = m ^ t * t ^ b := by
              rw [← mul_assoc, ← pow_add, hbr]
          _ ≤ (𝒩.card * s ^ t) * t ^ b := Nat.mul_le_mul hNst le_rfl
          _ = 𝒩.card * (t ^ b * s ^ t) := by ring
          _ ≤ 𝒩.card * ((b ^ b * Nat.choose t b) * s ^ t) :=
              Nat.mul_le_mul le_rfl (Nat.mul_le_mul hL1 le_rfl)
          _ = (𝒩.card * Nat.choose t b) * (b ^ b * s ^ t) := by ring
          _ ≤ (ℐ.card * Nat.choose m b) * (b ^ b * s ^ t) :=
              Nat.mul_le_mul hXc le_rfl
          _ = ℐ.card * ((Nat.choose m b * b ^ b) * s ^ t) := by ring
          _ ≤ ℐ.card * ((3 * m) ^ b * s ^ t) :=
              Nat.mul_le_mul le_rfl (Nat.mul_le_mul e1 le_rfl)
          _ = m ^ b * (ℐ.card * 3 ^ b * s ^ t) := by rw [mul_pow]; ring
      exact Nat.le_of_mul_le_mul_left e2 (Nat.pow_pos hm)
    -- `(3|W'|)^r ≥ r^r·c`, where `r^r ≤ 3^r·r!` supplies the missing `t` factor.
    have hW' : r ^ r * ℐ.card ≤ (3 * W'.card) ^ r := by
      calc r ^ r * ℐ.card ≤ r ^ r * Nat.choose W'.card r :=
            Nat.mul_le_mul le_rfl hchoose
        _ ≤ (3 ^ r * r.factorial) * Nat.choose W'.card r :=
            Nat.mul_le_mul (pow_le_three_pow_factorial r) le_rfl
        _ = 3 ^ r * (r.factorial * Nat.choose W'.card r) := by ring
        _ = 3 ^ r * W'.card.descFactorial r := by
            rw [Nat.descFactorial_eq_factorial_mul_choose]
        _ ≤ 3 ^ r * W'.card ^ r := Nat.mul_le_mul le_rfl (Nat.descFactorial_le_pow _ _)
        _ = (3 * W'.card) ^ r := (mul_pow _ _ _).symm
    -- `(rm)^r · t^b ≤ (3|W'|)^r · 3^b · s^t` (★).
    have hstar : (r * m) ^ r * t ^ b ≤ (3 * W'.card) ^ r * 3 ^ b * s ^ t := by
      calc (r * m) ^ r * t ^ b = r ^ r * (m ^ r * t ^ b) := by
            rw [mul_pow, mul_assoc]
        _ ≤ r ^ r * (ℐ.card * 3 ^ b * s ^ t) := Nat.mul_le_mul le_rfl hc
        _ = (r ^ r * ℐ.card) * 3 ^ b * s ^ t := by ring
        _ ≤ (3 * W'.card) ^ r * 3 ^ b * s ^ t :=
            Nat.mul_le_mul (Nat.mul_le_mul hW' le_rfl) le_rfl
    -- case on the parity of `t` and take `r`-th roots.
    rcases (show t = 2 * b ∨ t = 2 * b + 1 from by omega) with htE | htO
    · -- even `t = 2b`: `(rmt)^r ≤ (9|W'|s²)^r`, so `mt² ≤ 18|W'|s²`.
      have hrr : r = b := by omega
      have hp : (r * m * t) ^ r ≤ (9 * W'.card * s ^ 2) ^ r := by
        calc (r * m * t) ^ r = (r * m) ^ r * t ^ r := by rw [mul_pow]
          _ = (r * m) ^ r * t ^ b := by rw [show t ^ r = t ^ b from by rw [hrr]]
          _ ≤ (3 * W'.card) ^ r * 3 ^ b * s ^ t := hstar
          _ = (9 * W'.card * s ^ 2) ^ r := by
              rw [show t = 2 * r from by omega, pow_mul, ← hrr,
                show (9 * W'.card * s ^ 2) ^ r
                  = (3 * W'.card) ^ r * (3 * s ^ 2) ^ r from by
                    rw [show 9 * W'.card * s ^ 2 = 3 * W'.card * (3 * s ^ 2) from by ring,
                      mul_pow],
                mul_pow]
              ring
      have hroot : r * m * t ≤ 9 * W'.card * s ^ 2 :=
        (Nat.pow_le_pow_iff_left (by omega : r ≠ 0)).mp hp
      calc m * t ^ 2 = 2 * (r * m * t) := by
            rw [show m * t ^ 2 = m * t * t from by ring,
              show t = 2 * r from by omega]
            ring
        _ ≤ 2 * (9 * W'.card * s ^ 2) := Nat.mul_le_mul le_rfl hroot
        _ = 18 * (W'.card * s ^ 2) := by ring
        _ ≤ W'.card * (36 * s ^ 2) := by
            calc 18 * (W'.card * s ^ 2) = W'.card * s ^ 2 * 18 := by ring
              _ ≤ W'.card * s ^ 2 * 36 :=
                  Nat.mul_le_mul le_rfl (by omega : 18 ≤ 36)
              _ = W'.card * (36 * s ^ 2) := by ring
    · -- odd `t = 2b+1`: `(36|W'|s²)^r·3^{r-1} ≥ (mt²)^r·3^{r-1}`.
      have hrb : b = r - 1 ∧ t = 2 * r - 1 := by omega
      have hstar' : (r * m) ^ r * t ^ (r - 1)
          ≤ (3 * W'.card) ^ r * 3 ^ (r - 1) * s ^ (2 * r - 1) := by
        rw [← hrb.1, ← hrb.2]
        exact hstar
      have h12 : 3 ^ (r - 1) * t ^ (r + 1) ≤ (12 * r) ^ r * s := by
        have e1 : (3 * t) ^ r ≤ (12 * r) ^ r := Nat.pow_le_pow_left (by omega) r
        have e2 : 3 ^ (r - 1) * t ^ (r + 1) ≤ 3 ^ r * t ^ r * t := by
          calc 3 ^ (r - 1) * t ^ (r + 1)
              = (3 ^ (r - 1) * t ^ r) * t := by rw [pow_succ']; ring
            _ ≤ (3 ^ r * t ^ r) * t :=
                Nat.mul_le_mul
                  (Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (Nat.sub_le r 1))
                    le_rfl)
                  le_rfl
        calc 3 ^ (r - 1) * t ^ (r + 1) ≤ (3 * t) ^ r * t := by
              calc 3 ^ (r - 1) * t ^ (r + 1) ≤ 3 ^ r * t ^ r * t := e2
                _ = (3 * t) ^ r * t := by rw [mul_pow]
          _ ≤ (12 * r) ^ r * s := Nat.mul_le_mul e1 (by omega)
      have hfin : (m * t ^ 2) ^ r * 3 ^ (r - 1)
          ≤ (W'.card * (36 * s ^ 2)) ^ r * 3 ^ (r - 1) := by
        calc (m * t ^ 2) ^ r * 3 ^ (r - 1)
            = m ^ r * t ^ (r - 1) * (3 ^ (r - 1) * t ^ (r + 1)) := by
              rw [mul_pow, ← pow_mul,
                show t ^ (2 * r) = t ^ (r - 1) * t ^ (r + 1) from by
                  rw [← pow_add]; congr 1; omega]
              ring
          _ ≤ m ^ r * t ^ (r - 1) * ((12 * r) ^ r * s) := Nat.mul_le_mul le_rfl h12
          _ = ((r * m) ^ r * t ^ (r - 1)) * (12 ^ r * s) := by
              rw [mul_pow, mul_pow]; ring
          _ ≤ ((3 * W'.card) ^ r * 3 ^ (r - 1) * s ^ (2 * r - 1)) * (12 ^ r * s) :=
              Nat.mul_le_mul hstar' le_rfl
          _ = (W'.card * (36 * s ^ 2)) ^ r * 3 ^ (r - 1) := by
              have hs' : s ^ (2 * r - 1) * s = (s ^ 2) ^ r := by
                rw [← pow_succ, ← pow_mul]
                congr 1
                omega
              calc ((3 * W'.card) ^ r * 3 ^ (r - 1) * s ^ (2 * r - 1)) * (12 ^ r * s)
                  = (3 * W'.card) ^ r * 12 ^ r * (s ^ (2 * r - 1) * s)
                      * 3 ^ (r - 1) := by ring
                _ = (3 * W'.card) ^ r * 12 ^ r * (s ^ 2) ^ r * 3 ^ (r - 1) := by
                    rw [hs']
                _ = (W'.card * (36 * s ^ 2)) ^ r * 3 ^ (r - 1) := by
                    rw [show W'.card * (36 * s ^ 2) = (3 * W'.card) * (12 * s ^ 2) from
                          by ring,
                      mul_pow, mul_pow]
                    ring
      exact (Nat.pow_le_pow_iff_left (by omega : r ≠ 0)).mp
        (Nat.le_of_mul_le_mul_right hfin (Nat.pow_pos (by omega : 0 < 3)))

end SimpleGraph
