import Mathlib.Tactic
import Mathlib.Algebra.Field.Power
-- import Solutions.«Section-7-1»

/-!
# 7.2. Infinite series

Source: https://teorth.github.io/analysis/Analysis/Section_7_2/.

As before, I will reformulate the exercises to match definitions that are closer to mathlib and easier to work with.

We immediately diverge from the material and define a series as a sequence `ℕ → ℝ`.
-/

/-
These are mathlib names of some relevant results from 7-1
-/
#check Finset.sum_Icc_succ_top -- sum_of_nonempty
#check Finset.sum_Ico_consecutive -- concat_sum
#check Finset.sum_Ico_add_right_sub_eq -- shift_sum
#check Finset.abs_sum_le_sum_abs -- abs_sum_le_sum_abs_Icc

open Finset in
theorem sum_of_empty [Preorder α] [LocallyFiniteOrder α] [AddCommMonoid β] {n m:α} (h: n < m) (a: α → β) : ∑ i ∈ Icc m n, a i = 0 := by
  rw [Icc_eq_empty_iff.mpr (by grind)]
  exact sum_empty

/-
This is glue between Ico and Icc
-/
#check Finset.sum_Ico_add_eq_sum_Icc

section convergence

open Finset

/--
The sequence `S` of partial sums of `s`: `S (n + 1) = s 0 + ··· + s n`.
-/
def partials (s : ℕ → ℝ) (N:ℕ) : ℝ := ∑ n ∈ range N, s n

lemma partials_def : partials s N = ∑ n ∈ range N, s n := rfl

theorem partials_succ (s : ℕ → ℝ) {N:ℕ} : partials s (N + 1) = partials s N + s N := by
  rw [partials_def, sum_range_succ]
  rfl

/-
An alternative definition
-/
def partialsIcc (s : ℕ → ℝ) (N:ℕ) : ℝ := ∑ n ∈ Icc 0 N, s n

lemma partialsIcc_def : partialsIcc s N = ∑ n ∈ Icc 0 N, s n := rfl

/-
Shifting
-/
def shift (m : ℤ) (s : ℕ → ℝ) (n : ℕ) := if n < m then 0 else s (n - m).toNat

lemma shift_def : shift m s = fun n : ℕ => if n < m then 0 else s (n - m).toNat := rfl

lemma shift_apply : shift m s n = if n < m then 0 else s (n - m).toNat := rfl

theorem partials_shift_of_lt {s : ℕ → ℝ} {N:ℕ} (h : N < m) : partials (shift m s) N = 0 := by
  classical
  simp [partials_def, shift_apply]
  rw [sum_ite_of_true]
  · simp
  · grind

/-
Convergence
-/

open Filter Topology

def HasSum' (s : ℕ → ℝ) (L : ℝ) := Tendsto (partials s) atTop (𝓝 L)

def Summable' (s : ℕ → ℝ) := ∃ L, HasSum' s L

-- TODO connect HasSum and HasSum'
#check HasSum

open Classical in
noncomputable def tsum' (s : ℕ → ℝ) : ℝ := if h : Summable' s then h.choose else 0

#check tsum

lemma tsum_summable (h : Summable' s) : tsum' s = h.choose := by
  unfold tsum'
  grind

lemma summable_spec (h : Summable' s) : Tendsto (partials s) atTop (𝓝 h.choose) := Exists.choose_spec h

lemma partials_tendsto_of_summable (h : Summable' s) : Tendsto (partials s) atTop (𝓝 (tsum' s)) := by
  rw [tsum_summable h]
  exact Exists.choose_spec h

theorem summable_of_hasSum (h : HasSum' s L) : Summable' s := by
  use L

#check Summable.hasSum

theorem tsum_eq_of_hasSum (h : HasSum' s L) : tsum' s = L := by
  rw [tsum_summable (summable_of_hasSum h)]
  apply tendsto_nhds_unique _ h
  apply summable_spec

theorem hasSum_uniq (h1 : HasSum' s L) (h2 : HasSum' s L') : L = L' := by
  exact tendsto_nhds_unique h1 h2
  -- rw [← tsum_eq_of_hasSum h1, ← tsum_eq_of_hasSum h2] -- also works

theorem hasSum_of_summable (h : Summable' s) : HasSum' s (tsum' s) := by
  rw [tsum_summable h]
  exact summable_spec h

theorem Series.example_7_2_4a (N:ℕ) : partials (fun n ↦ (2:ℝ)^(-(n + 1):ℤ)) N = 1 - (2:ℝ)^(-(N : ℤ)) := by
  rw [partials_def]
  induction N with
  | zero =>
    norm_num
  | succ n ih =>
    rw [sum_range_succ, ih]
    norm_cast
    simp
    ring

theorem Series.example_7_2_4b : HasSum' (fun n ↦ (2:ℝ)^(-(n + 1):ℤ)) 1 := by
  unfold HasSum'
  rw [funext example_7_2_4a]
  nth_rw 2 [show (1 : ℝ) = 1 - 0 by simp]
  apply Tendsto.const_sub
  rw [Metric.tendsto_atTop]
  intro ε εh
  use ⌈- Real.log (ε / 2) / Real.log 2⌉₊
  intro n hn
  simp at hn
  rw [Real.dist_eq, abs_of_nonneg, sub_zero]
  · rw [Real.zpow_lt_iff_lt_log (by simp) εh]
    zify
    calc -n * Real.log 2
      _ ≤ Real.log (ε/2) / Real.log 2 * Real.log 2 := by grw [← hn]; grind
      _ = Real.log (ε/2) := by norm_num
      _ < Real.log ε := by apply Real.log_lt_log <;> grind
  · norm_cast
    simp

theorem Series.example_7_2_4c : tsum' (fun n ↦ (2:ℝ)^(-(n + 1):ℤ)) = 1 := by
  exact tsum_eq_of_hasSum example_7_2_4b

theorem Series.example_7_2_4'a {N:ℕ} : partials (fun n ↦ (2:ℝ)^(n:ℤ)) N = (2:ℝ)^N - 1 := by
  rw [partials_def]
  induction N with
  | zero =>
    norm_num
  | succ n ih =>
    rw [sum_range_succ, ih]
    norm_cast
    grind

lemma Nat.le_pow_self (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Nat.two_pow_succ]
    apply add_le_add ih
    exact Nat.one_le_two_pow

theorem Series.example_7_2_4'b : ¬ Summable' (fun n ↦ (2:ℝ)^(n:ℤ)) := by
  unfold Summable'
  push Not
  intro l
  unfold HasSum'
  apply not_tendsto_nhds_of_tendsto_atTop
  apply tendsto_atTop_atTop_of_monotone
  · intro x y h
    simp [partials_def]
    apply sum_mono_set_of_nonneg (by simp)
    exact range_subset_range.mpr h
  · intro x
    use (⌈x⌉₊ + 1)
    rw [partials_def]
    rw [sum_range_succ]
    have : ∑ k ∈ range ⌈x⌉₊, (2 : ℝ) ^ (k : ℤ) ≥ 0
    · apply sum_nonneg
      simp
    grw [this]
    rw [zero_add]
    by_cases hx : x ≤ 0
    · rw [Nat.ceil_eq_zero.mpr hx]
      simp
      grind
    · rw [not_le] at hx
      apply le_trans (Nat.le_ceil _)
      exact_mod_cast Nat.le_pow_self _

lemma sum_Ico_eq_partials_sub {s : ℕ → ℝ} {p q} (hpq : p ≤ q) : ∑ n ∈ Ico p q, s n = partials s q - partials s p := by
  induction q, hpq using Nat.le_induction with
  | base =>
    simp
  | succ q hpq ih =>
    rw [sum_Ico_succ_top hpq, ih]
    simp [partials_def, sum_range_succ]
    ring

lemma sum_Ioc_eq_partialsIcc_sub {s : ℕ → ℝ} {p q} (hpq : p ≤ q) : ∑ n ∈ Ioc p q, s n = partialsIcc s q - partialsIcc s p := by
  induction q, hpq using Nat.le_induction with
  | base =>
    simp
  | succ q hpq ih =>
    rw [sum_Ioc_succ_top hpq, ih]
    simp [partialsIcc_def, sum_Icc_succ_top]
    ring

/--
## Cauchy criterion for series

We use `∑ n ∈ Ico p q` so that it matches `partials s q - partials s p`.
Also `q ≥ p` because it makes life easier.

- `Filter.Tendsto.cauchySeq`
- `Metric.cauchySeq_iff`

Hints:
- ⇒-direction `apply Filter.Tendsto.cauchySeq at h` and use `Metric.cauchySeq_iff`
- ⇐-direction: start with `apply cauchySeq_tendsto_of_complete` and use `Metric.cauchySeq_iff`
-/
theorem summable_iff_tail_decay_Ico' {s : ℕ → ℝ} :
    Summable' s ↔ ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ p, |∑ n ∈ Ico p q, s n| < ε := by
  constructor
  · intro h ε hε
    obtain ⟨L, h⟩ := h
    apply Filter.Tendsto.cauchySeq at h
    rw [Metric.cauchySeq_iff] at h
    specialize h ε hε
    obtain ⟨N, hN⟩ := h
    refine ⟨N, ?_⟩
    intro p hp q hq
    specialize hN p hp q (by grind)
    rw [sum_Ico_eq_partials_sub hq, abs_sub_comm]
    exact hN
  · intro h
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    specialize h ε hε
    obtain ⟨N, hN⟩ := h
    refine ⟨N, ?_⟩
    intro p hp q hq
    specialize hN (min p q) (by grind) (max p q) (by grind)
    rw [sum_Ico_eq_partials_sub min_le_max] at hN
    by_cases hpq : p ≤ q
    · rw [max_eq_right hpq, min_eq_left hpq, abs_sub_comm] at hN
      exact hN
    · rw [max_eq_left (by grind), min_eq_right (by grind)] at hN
      exact hN

/-
This is a more standard version, expressed as a corollary
-/
theorem summable_iff_tail_decay_Ico {s : ℕ → ℝ} :
    Summable' s ↔ ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |∑ n ∈ Ico p q, s n| < ε := by
  rw [summable_iff_tail_decay_Ico']
  constructor
  · intro h ε hε
    specialize h ε hε
    obtain ⟨N, h⟩ := h
    refine ⟨N, ?_⟩
    intro p hp q hq
    by_cases hpq : p ≤ q
    · exact h p hp q hpq
    · simpa [show Ico p q = ∅ by grind]
  · intro h ε hε
    specialize h ε hε
    obtain ⟨N, h⟩ := h
    refine ⟨N, ?_⟩
    grind

/-
Ioc version for completeness
-/
theorem summable_iff_tail_decay_Ioc {s : ℕ → ℝ} :
    Summable' s ↔ ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |∑ n ∈ Ioc p q, s n| < ε := by
  rw [summable_iff_tail_decay_Ico']
  constructor
  · intro h ε hε
    specialize h ε hε
    obtain ⟨N, h⟩ := h
    refine ⟨N, ?_⟩
    intro p hp q hq
    by_cases hpq : p ≤ q
    · simp_rw [← Ico_add_one_add_one_eq_Ioc]
      grind
    · simpa [show Ioc p q = ∅ by grind]
  · intro h ε hε
    specialize h ε hε
    obtain ⟨N, h⟩ := h
    refine ⟨N + 1, ?_⟩
    intro p hp q hq
    rw [← Ioc_sub_one_sub_one_eq_Ico_of_not_isMin (by simp; grind)]
    exact h (p - 1) (by grind) (q - 1) (by grind)

/-
This is the standard (Icc) version
-/
theorem summable_iff_tail_decay {s : ℕ → ℝ} :
    Summable' s ↔ ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |∑ n ∈ Icc p q, s n| < ε := by
  rw [summable_iff_tail_decay_Ioc]
  constructor
  · intro h ε hε
    specialize h ε hε
    obtain ⟨N, h⟩ := h
    refine ⟨N+1, ?_⟩
    intro p hp q hq
    specialize h (p-1) (by grind) q (by grind)
    rw [show p = p - 1 + 1 by grind, Icc_add_one_left_eq_Ioc]
    exact h
  · intro h ε hε
    specialize h ε hε
    obtain ⟨N, h⟩ := h
    refine ⟨N, ?_⟩
    intro p hp q hq
    specialize h (p+1) (by grind) q (by grind)
    rw [Icc_add_one_left_eq_Ioc] at h
    exact h

theorem decay_of_summable {s : ℕ → ℝ} (h : Summable' s) : Tendsto s atTop (𝓝 0) := by
  rw [summable_iff_tail_decay] at h
  rw [Metric.tendsto_atTop]
  intro ε hε
  specialize h ε hε
  obtain ⟨N, h⟩ := h
  refine ⟨N, ?_⟩
  intro n hn
  specialize h n hn n hn
  rw [Icc_self, sum_singleton, ← sub_zero (s n)] at h
  exact h

theorem diverges_of_nodecay {s : ℕ → ℝ} (h : ¬ Tendsto s atTop (𝓝 0)) : ¬ Summable' s := by
  contrapose h
  exact decay_of_summable h

/-
Equivalent definition of convergence using partialsIcc.

The ⇒ proof is easy with subsequence convergence, ⇐ is straight-forward `Metric.tendsto_atTop`
-/
theorem hasSum_partialsIcc : HasSum' s L ↔ Tendsto (partialsIcc s) atTop (𝓝 L) := by
  change Tendsto (fun _ => _) _ _ ↔ Tendsto (fun _ => _) _ _
  simp_rw [partialsIcc_def, partials_def, range_eq_Ico]
  constructor
  · intro h
    apply tendsto_iff_seq_tendsto.mp h (· + 1) (tendsto_add_atTop_nat 1)
  · intro h
    rw [Metric.tendsto_atTop] at *
    intro ε hε
    specialize h ε hε
    obtain ⟨N, h⟩ := h
    refine ⟨N + 1, ?_⟩
    intro n hn
    specialize h (n - 1) (by grind)
    rw [Icc_sub_one_right_eq_Ico_of_not_isMin (by simp; grind)] at h
    exact h

theorem summable_partialsIcc : Summable' s ↔ ∃ L, Tendsto (partialsIcc s) atTop (𝓝 L) := by
  simp_rw [← hasSum_partialsIcc]
  rfl

theorem Series.example_7_2_7 : ¬ Summable' (fun _ ↦ 1) := by
  apply diverges_of_nodecay
  simp

theorem Series.example_7_2_7' : ¬ Summable' (fun n:ℕ ↦ (-1:ℝ)^n) := by
  apply diverges_of_nodecay
  -- simp -- would use tendsto_pow_atTop_nhds_zero_iff
  intro h
  rw [Metric.tendsto_atTop] at h
  specialize h (1/2) (by grind)
  obtain ⟨N, h⟩ := h
  specialize h N le_rfl
  norm_num at h

/-
The absolute value of a function is simply taken pointwise.

I don't see a reason to define absolute convergence separately.
-/
example {s : ℕ → ℝ} : |s| = fun n => |s n| := rfl

def CondSummable (s : ℕ → ℝ) := Summable' s ∧ ¬ Summable' |s|

lemma abs_sum_abs_eq {a : ℕ → ℝ} : |∑ n ∈ s, abs (a n)| = ∑ n ∈ s, |a n| := by
  rw [abs_eq_self]
  apply sum_nonneg
  simp

/-
You might need `Pi.abs_apply`

Hints:
1. Start with rewriting `summable_iff_tail_decay_Ioc` and `abs_sum_le_sum_abs`
-/
theorem summable_of_abs_summable (h : Summable' |s|) : Summable' s := by
  -- obtain ⟨L, h⟩ := h
  rw [summable_iff_tail_decay_Ioc] at h ⊢
  intro ε hε
  specialize h ε hε
  obtain ⟨N, h⟩ := h
  refine ⟨N, ?_⟩
  intro p hp q hq
  specialize h p hp q hq
  grw [abs_sum_le_sum_abs]
  simp_rw [Pi.abs_apply] at h
  rw [abs_sum_abs_eq] at h
  exact h

/-
This is also an application of `abs_sum_le_sum_abs`
-/
lemma partials_abs_le (N) : |partials s N| ≤ partials |s| N := by
  rw [partials_def, partials_def]
  apply abs_sum_le_sum_abs

/-
`le_of_tendsto_of_tendsto'` or the stronger `le_of_tendsto_of_tendsto`
-/
theorem abs_tsum_le (h : Summable' |s|) : |tsum' s| ≤ tsum' |s| := by
  have h2 := summable_of_abs_summable h
  obtain ⟨L, h⟩ := h
  obtain ⟨L2, h2⟩ := h2
  rw [tsum_eq_of_hasSum h, tsum_eq_of_hasSum h2]
  unfold HasSum' at *
  apply Tendsto.abs at h2
  apply le_of_tendsto_of_tendsto' h2 h
  intro N
  exact partials_abs_le N

/-
These lemmas are useful in my proof of the alternating series test
-/
lemma dist_partialsIcc_eq {a : ℕ → ℝ} (a_nonneg : 0 ≤ a) {m} : dist (partialsIcc (fun n => (-1) ^ n * a n) (2 * m)) (partialsIcc (fun n => (-1) ^ n * a n) (2 * m + 1)) = a (2 * m + 1) := by
  rw [Real.dist_eq, abs_sub_comm]
  simp [← sum_Ioc_eq_partialsIcc_sub]
  apply a_nonneg

lemma partialsIcc_even_succ_le {a : ℕ → ℝ} (a_nonneg : 0 ≤ a) {m} : partialsIcc (fun n => (-1 : ℝ) ^ n * a n) (2 * m + 1) ≤ partialsIcc (fun n => (-1) ^ n * a n) (2 * m) := by
  simp [partialsIcc_def, sum_Icc_succ_top]
  rw [Odd.neg_one_pow (by grind)]
  simp
  apply a_nonneg

lemma partialsIcc_odd_le_succ {a : ℕ → ℝ} (a_nonneg : 0 ≤ a) {m} : partialsIcc (fun n => (-1 : ℝ) ^ n * a n) (2 * m + 1) ≤ partialsIcc (fun n => (-1) ^ n * a n) (2 * m + 2) := by
  simp [partialsIcc_def, sum_Icc_succ_top]
  rw [Even.neg_one_pow (by grind)]
  simp
  apply a_nonneg

/-
## Alternating series test (Leibniz's test)

My proof roughly follows https://en.wikipedia.org/wiki/Alternating_series_test#Proof_of_the_alternating_series_test

We denote the partial sums with `Sₙ = ∑ m ∈ 0..n, (-1)ᵐ aₘ`.
Notice that we need to use the `partialsIcc` definition via `summable_partialsIcc` for following to work.

We start by defining sequences for the odd and even partial sums.

`even: 0, a₀ - a₁, a₀ - a₁, a₀ - a₁ + a₂ - a₃, a₀ - a₁ + a₂ - a₃, ...`
`odd: a₀, a₀, a₀ - a₁ + a₂, a₀ - a₁ + a₂, ...`

It's easy to see that `odd n - even n = aₙ` (`odd_sub_even`).
The two lemmas `even_succ` and `odd_succ` turn out to be surprisingly useful when showing `even_mono` and `odd_anti`.

The limit of `even` and `odd` is `⨅ i, odd i`, because `|odd n - even n|` tends to zero.
As `even n ≤ Sₙ ≤ odd n`, the squeeze theorem (which is missing in the wikipedia proof) gives us convergence.

The following API is useful
- When splitting into cases `Odd n`/`Even n`, one can use `Nat.not_odd_iff_even` and `Nat.not_even_iff_odd`
- `monotone_nat_of_le_succ` and `antitone_nat_of_succ_le`
- `tendsto_atTop_ciInf`
- `Tendsto.congr_dist`
- `Tendsto.squeeze`
-/
theorem summable_alternating_of_antitone {a : ℕ → ℝ} (a_nonneg : 0 ≤ a) (a_antitone : Antitone a) (a_tendsto_zero : Tendsto a atTop (𝓝 0))
    : Summable' (fun n => (-1)^n * a n) := by
  rw [summable_partialsIcc]
  let S := partialsIcc (fun m => (-1)^m * a m)

  -- even needs to start at zero otherwise it includes partials 0 = a₀
  -- even: 0, a₀ - a₁, a₀ - a₁, a₀ - a₁ + a₂ - a₃, a₀ - a₁ + a₂ - a₃, ...
  let even (n) := if n = 0 then 0 else S (2*((n - 1)/2) + 1)

  -- odd: a₀, a₀, a₀ - a₁ + a₂, a₀ - a₁ + a₂, ...
  let odd (n) := S (2*(n/2))

  have even_succ {n} (hn : Odd n) : even n = even (n + 1)
  · obtain ⟨n, rfl⟩ := hn
    unfold even
    simp [show (2 * n + 1) / 2 = n by omega]

  have odd_succ {n} (hn : Even n) : odd n = odd (n + 1)
  · obtain ⟨n, rfl⟩ := hn
    unfold odd
    simp [← two_mul, show (2 * n + 1) / 2 = n by omega]

  have odd_sub_even (n) : odd n - even n = a n
  · unfold odd even S
    by_cases hn : Odd n
    · obtain ⟨n, rfl⟩ := hn
      simp [show (2 * n + 1) / 2 = n by omega]
      rw [← neg_sub, ← sum_Ioc_eq_partialsIcc_sub]
      · simp
        rw [Odd.neg_one_pow (by grind)]
        simp
      simp
    · rw [Nat.not_odd_iff_even] at hn
      obtain ⟨n, rfl⟩ := hn
      simp [← two_mul]
      split
      · subst n
        simp [partialsIcc_def]
      · simp [show (2 * n - 1) / 2 = n - 1 by omega, show 2 * (n - 1) + 1 = 2 * n - 1 by omega]
        rw [← sum_Ioc_eq_partialsIcc_sub (by simp), show Ioc (2 * n - 1) (2 * n) = {2 * n} by grind]
        simp

  -- We don't need to unfold partials after this point

  have even_mono : Monotone even
  · apply monotone_nat_of_le_succ
    intro n
    by_cases hn : Odd n
    · grw [even_succ hn]
    · rw [Nat.not_odd_iff_even] at hn
      have := odd_sub_even n
      rw [odd_succ hn] at this
      have := odd_sub_even (n + 1)
      have : a (n + 1) ≤ a n := a_antitone (by simp)
      linarith

  have odd_anti : Antitone odd
  · apply antitone_nat_of_succ_le
    intro n
    by_cases hn : Even n
    · grw [odd_succ hn]
    · rw [Nat.not_even_iff_odd] at hn
      have := odd_sub_even n
      rw [even_succ hn] at this
      have := odd_sub_even (n + 1)
      have : a (n + 1) ≤ a n := a_antitone (by simp)
      linarith

  have partials_eq_even {m} (hm : Odd m) : partialsIcc (fun n => (-1)^n * a n) m = even m
  · obtain ⟨n, rfl⟩ := hm
    unfold even S
    simp

  have partials_eq_odd {m} (hm : Even m) : partialsIcc (fun n => (-1)^n * a n) m = odd m
  · obtain ⟨n, rfl⟩ := hm
    unfold odd S
    simp +arith

  have partials_one_le_odd {m} : partialsIcc (fun n => (-1)^n * a n) 1 ≤ partialsIcc (fun n => (-1)^n * a n) (2 * m + 1)
  · rw [partials_eq_even (by simp), partials_eq_even (by simp)]
    exact even_mono (by simp)

  have even_le_odd {n} : even n ≤ odd n
  · have := odd_sub_even n
    have : 0 ≤ a n
    · apply a_nonneg
    linarith

  have odd_bddBelow : BddBelow (Set.range odd)
  · rw [bddBelow_def]
    use even 0 -- = 0
    intro y hy
    rw [Set.mem_range] at hy
    obtain ⟨n, rfl⟩ := hy
    grw [← even_le_odd, even_mono (by simp)]

  have lim_even := tendsto_atTop_ciInf odd_anti odd_bddBelow

  set L := ⨅ i, odd i

  have dist_even_odd {n} : dist (odd n) (even n) = a n
  · rw [Real.dist_eq, odd_sub_even, abs_of_nonneg (a_nonneg _)]

  -- difference goes to zero by s_tendsto_zero
  have lim_odd : Tendsto even atTop (𝓝 L)
  · apply Tendsto.congr_dist lim_even
    simp_rw [dist_even_odd]
    exact a_tendsto_zero

  use L

  apply Tendsto.squeeze lim_odd lim_even
  · intro n
    by_cases hn : Odd n
    · rw [partials_eq_even hn]
    · rw [Nat.not_odd_iff_even] at hn
      rw [partials_eq_odd hn]
      exact even_le_odd
  · intro n
    by_cases hn : Even n
    · rw [partials_eq_odd hn]
    · rw [Nat.not_even_iff_odd] at hn
      rw [partials_eq_even hn]
      exact even_le_odd

section

/-
Some useful results for shifting needed soon
-/

namespace Finset

variable {α G M : Type*}
variable [CommMonoid M] {s₂ s₁ s : Finset α} {a : α} {g f : α → M}

-- Missing in mathlib
@[to_additive (attr := simp)]
theorem prod_Ioc_add_right_sub_eq [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    [ExistsAddOfLE α] [LocallyFiniteOrder α] [Sub α] [OrderedSub α] (a b c : α) :
    ∏ x ∈ Ioc (a + c) (b + c), f (x - c) = ∏ x ∈ Ioc a b, f x := by
  simp only [← map_add_right_Ioc, prod_map, addRightEmbedding_apply, add_tsub_cancel_right]

end Finset

#check Ico_succ_succ_eq_Ioc

theorem Int.toNat_cast_sub {n : ℕ} {m : ℤ} (h : n ≥ m) : (n - m).toNat = n - m := by
  omega

/-
Hints:
1. Start with `summable_iff_tail_decay_Ioc'`
2. As choice of `N` use `N + n.toNat`
3. Use `sum_Ioc_add_right_sub_eq` to unify `h` with the goal
-/
-- theorem summable_shift {s : ℕ → ℝ} (h : Summable' s) : Summable' (shift n s) := by
--   rw [summable_iff_tail_decay_Ioc'] at *
--   intro ε hε
--   specialize h ε hε
--   obtain ⟨N, h⟩ := h
--   refine ⟨N + n.toNat, ?_⟩
--   intro p hp q qh
--   by_cases hn : 0 ≤ n
--   · lift n to ℕ using hn
--     simp [shift_apply]
--     rw [sum_ite_of_false (by grind)]
--     specialize h (p - n) (by grind) (q - n) (by grind)
--     rw [← sum_Ioc_add_right_sub_eq (c := n)] at h
--     rw [show p - n + n = p by grind, show q - n + n = q by grind] at h
--     exact h
--   · simp [shift_apply]
--     rw [sum_ite_of_false (by grind)]
--     simp_rw [sub_eq_add_neg]

--     -- Let's lift -n to ℕ
--     rw [not_le] at hn
--     apply le_of_lt at hn
--     rw [← neg_nonneg] at hn
--     simp [show n.toNat = 0 by grind] at hp
--     generalize -n = m at * -- set doesn't work here because it leaves a defeq
--     lift m to ℕ using hn

--     specialize h (p + m) (by grind) (q + m) (by grind)
--     rw [← sum_Ioc_add_right_sub_eq (c := m)]
--     convert h
--     grind

-- theorem summable_iff_summable_shift {s : ℕ → ℝ} : Summable' s ↔ Summable' (shift n s) := by
--   refine ⟨summable_shift, ?_⟩
--   intro h
--   rw [summable_iff_tail_decay_Ioc'] at *
--   intro ε hε
--   specialize h ε hε
--   obtain ⟨N, h⟩ := h
--   refine ⟨(N - n).toNat, ?_⟩
--   intro p hp q qh

-- theorem shift_nat_eq_comp {n : ℕ} {s} : shift (-n) s = s ∘ (fun m => m + n) := by
--   ext m
--   simp [shift_apply]
--   grind

theorem hasSum_const_mul_left {a} (h : HasSum' a L) : HasSum' (fun n => c * a n) (c * L) := by
  change Tendsto (fun _ => _) _ _
  simp_rw [partials_def, ← mul_sum]
  exact Tendsto.const_mul _ h

theorem summable_const_mul_left {a} (h : Summable' a) : Summable' (fun n => c * a n) := by
  obtain ⟨L, h⟩ := h
  use c * L
  exact hasSum_const_mul_left h

/-
Variant of alternating series test
-/
theorem summable_alternating_of_antitone' {a : ℕ → ℝ} (a_nonneg : 0 ≤ a) (a_antitone : Antitone a) (a_tendsto_zero : Tendsto a atTop (𝓝 0))
    : Summable' (fun n => (-1)^(n + 1) * a n) := by
  simp [pow_add]
  simp_rw [neg_eq_neg_one_mul (_ * _)]
  apply summable_const_mul_left
  exact summable_alternating_of_antitone a_nonneg a_antitone a_tendsto_zero

noncomputable def example_7_2_13.s := fun (n : ℕ) => (-1 : ℝ)^(n + 1) / (↑(n + 1) : ℤ)

theorem example_7_2_13.a : Summable' s := by
  unfold s
  apply summable_alternating_of_antitone'
  · intro n
    simp
    grind
  · apply antitone_nat_of_succ_le
    intro n
    rw [inv_le_inv₀]
    · simp
    · simp
      grind
    · simp
      grind
  · apply Tendsto.comp tendsto_inv_atTop_zero
    simp
    apply tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_atTop

section
variable {ι α : Type*} {a a₁ a₂ b b₁ b₂ c x : α} [Preorder α] [LocallyFiniteOrder α]
@[simp]
theorem Ico_disjoint_Ico_of_le {d : α} (hbc : b ≤ c) : Disjoint (Ico a b) (Ico c d) :=
  disjoint_left.2 fun _ h1 h2 ↦ not_and_of_not_left _
    (by grind) (mem_Ico.1 h2)
end

/-
Grouping (without the requirement that φ 0 = 0).

The φ 0 requirement is only needed when actually comparing the sums.
It's not needed for convergence of the series.
-/
theorem sum_grouped {a : ℕ → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ) {p q : ℕ}
  : ∑ n ∈ Ico p q, ∑ k ∈ Ico (φ n) (φ (n + 1)), a k =
    ∑ k ∈ Ico (φ p) (φ q), a k := by
  by_cases hpq : p ≤ q
  · induction q, hpq using Nat.le_induction with
  | base =>
    simp
  | succ q hpq ih =>
    rw [sum_Ico_succ_top (by grind), ih, ← sum_union, Ico_union_Ico_eq_Ico]
    · apply hφ.monotone
      grind
    · apply hφ.monotone
      grind
    · simp
  · rw [not_le] at hpq
    have : φ q ≤ φ p
    · apply hφ.monotone
      omega
    simp [hpq.le, this]

lemma partials_grouped {a : ℕ → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ) : partials (fun n => ∑ k ∈ Ico (φ n) (φ (n + 1)), a k) N = ∑ k ∈ Ico (φ 0) (φ N), a k := by
  rw [partials_def, range_eq_Ico, sum_grouped hφ]

/-
This is an immediate consequence of convergence of subsequences `tendsto_iff_seq_tendsto`
-/
theorem hasSum_grouped {φ : ℕ → ℕ} (hφ : StrictMono φ) (hφ0 : φ 0 = 0) (h : HasSum' a L) : HasSum' (fun n => ∑ k ∈ Ico (φ n) (φ (n + 1)), a k) L := by
  change Tendsto (fun _ => _) _ _
  simp_rw [partials_grouped hφ, hφ0, ← range_eq_Ico]
  exact tendsto_iff_seq_tendsto.mp h _ hφ.tendsto_atTop

-- This `summable_grouped` is a direct consequence of `hasSum_grouped`, however hφ0 is an unnecessary assumption
example {φ : ℕ → ℕ} (hφ : StrictMono φ) (hφ0 : φ 0 = 0) (h : Summable' a) : Summable' (fun n => ∑ k ∈ Ico (φ n) (φ (n + 1)), a k) := by
  obtain ⟨L, h⟩ := h
  use L
  exact hasSum_grouped hφ hφ0 h

/-
This is quite easy to prove with Cauchy criterion and `sum_grouped`
-/
theorem summable_grouped {φ : ℕ → ℕ} (hφ : StrictMono φ) (h : Summable' a) : Summable' (fun n => ∑ k ∈ Ico (φ n) (φ (n + 1)), a k) := by
  rw [summable_iff_tail_decay_Ico] at h ⊢
  intro ε hε
  specialize h ε hε
  obtain ⟨N, h⟩ := h
  refine ⟨N, ?_⟩
  intro p hp q hq
  simp_rw [sum_grouped hφ]
  apply h (φ p) ?_ (φ q) ?_
  · grw [← hφ.le_apply]
    linarith
  · grw [← hφ.le_apply]
    linarith

/-
The other direction is more challenging.

Hint: show `Ico p q ⊆ Ico (φ N) (φ q)` and use `sum_mono_set_of_nonneg`
-/
theorem summable_of_summable_grouped (a_nonneg : 0 ≤ a) {φ : ℕ → ℕ} (hφ : StrictMono φ) (h : Summable' (fun n => ∑ k ∈ Ico (φ n) (φ (n + 1)), a k)) : Summable' a := by
  rw [summable_iff_tail_decay_Ico] at h ⊢
  intro ε hε
  specialize h ε hε
  obtain ⟨N, h⟩ := h
  refine ⟨φ N, ?_⟩
  intro p hp q hq
  simp_rw [sum_grouped hφ] at h
  specialize h N le_rfl q ?_
  · apply le_trans hφ.le_apply
    exact hq
  have : Ico p q ⊆ Ico (φ N) (φ q)
  · intro n hn
    simp at hn
    simp
    constructor
    · linarith
    · grw [← hφ.le_apply]
      linarith
  have := sum_mono_set_of_nonneg a_nonneg this
  simp only at this
  rw [abs_of_nonneg] at h ⊢
  · linarith
  · apply sum_nonneg
    intro i hi
    apply a_nonneg
  · apply sum_nonneg
    intro i hi
    apply a_nonneg

theorem summable_iff_summable_grouped (a_nonneg : 0 ≤ a) {φ : ℕ → ℕ} (hφ : StrictMono φ) : Summable' (fun n => ∑ k ∈ Ico (φ n) (φ (n + 1)), a k) ↔ Summable' a := by
  constructor
  · exact summable_of_summable_grouped a_nonneg hφ
  · exact summable_grouped hφ

theorem tsum_eq_tsum_grouped {φ : ℕ → ℕ} (hφ : StrictMono φ) (hφ0 : φ 0 = 0) (h : Summable' a) : tsum' a = tsum' (fun n => ∑ k ∈ Ico (φ n) (φ (n + 1)), a k) := by
  obtain ⟨L, h⟩ := h
  rw [tsum_eq_of_hasSum (hasSum_grouped hφ hφ0 h), tsum_eq_of_hasSum h]

theorem example_7_2_13.b : ¬ Summable' |s| := by
  let φ n := 2^n
  have hφ : StrictMono φ
  · apply strictMono_nat_of_lt_succ
    grind

  intro h
  have h2 := summable_grouped hφ h
  apply diverges_of_nodecay _ h2
  intro hf
  rw [Metric.tendsto_atTop] at hf
  specialize hf (1/4) (by simp)
  obtain ⟨N, hf⟩ := hf
  specialize hf N le_rfl

  -- Comment: this is one of the ugliest proofs ever
  have : 1/4 ≤ ∑ x ∈ Ico (φ N) (φ (N + 1)), (x + 1 : ℝ)⁻¹
  · calc
    _ ≤ 2^N * (2^N : ℝ)⁻¹ * (2^2 : ℝ)⁻¹ := by norm_num
    _ ≤ 2^N * (2^(N + 2) : ℝ)⁻¹ := by ring_nf; rfl
    _ ≤ 2^N * (2^(N + 1) + 1 : ℝ)⁻¹ := by
      simp
      rw [inv_le_inv₀]
      · have : (1 : ℝ) ≤ 2^(N + 1)
        · exact_mod_cast by grind
        grw [this]
        ring_nf
        rfl
      · exact_mod_cast by grind
      · exact_mod_cast by grind
    _ = ∑ x ∈ Ico (φ N) (φ (N + 1)), (φ (N + 1) + 1 : ℝ)⁻¹ := by simp [φ]; norm_cast; grind
    _ ≤ ∑ x ∈ Ico (φ N) (φ (N + 1)), (x + 1 : ℝ)⁻¹ := by
      apply sum_le_sum
      intro i hi
      rw [inv_le_inv₀]
      · simp
        simp at hi
        linarith
      · linarith
      · linarith

  simp [abs_div, s] at hf
  grind

theorem example_7_2_13.c : CondSummable s := by
  exact ⟨a, b⟩

/-
Series laws
-/

/-
## Cauchy condensation test

https://en.wikipedia.org/wiki/Cauchy_condensation_test

Steps:
0. Define strictly monotone `φ n = 2^n`
1. Apply `summable_of_summable_grouped`
2. Use Cauchy criterion (`summable_iff_tail_decay`) at `h` and the goal
3. Get rid of the extra absolute values with `abs_of_nonneg`
4. `apply lt_of_lt_of_le' h` and `sum_le_sum`
5. Show `2^i * a (2^i) = ∑ k ∈ Ico (φ i) (φ (i + 1)), a (2^i)`
6. `sum_le_sum` and `a_anti`
-/
theorem summable_of_condensed (a_nonneg : 0 ≤ a) (a_anti : Antitone a) (h : Summable' (fun n => 2^n * a (2^n))) : Summable' a := by
  let φ n := 2^n
  have hφ : StrictMono φ
  · apply strictMono_nat_of_lt_succ
    grind

  apply summable_of_summable_grouped a_nonneg hφ

  rw [summable_iff_tail_decay] at h ⊢
  intro ε hε
  specialize h ε hε
  obtain ⟨N, h⟩ := h
  refine ⟨N, ?_⟩
  intro p hp q hq
  specialize h p hp q hq

  rw [abs_of_nonneg] at h ⊢
  · apply lt_of_lt_of_le' h
    apply sum_le_sum
    intro i hi
    have : 2^i * a (2^i) = ∑ k ∈ Ico (φ i) (φ (i + 1)), a (2^i)
    · simp [φ]
      exact_mod_cast by grind
    rw [this]
    apply sum_le_sum
    intro j hj
    exact a_anti (mem_Ico.mp hj).left

  · apply sum_nonneg
    intro i hi
    apply sum_nonneg
    intro j hj
    apply a_nonneg
  · apply sum_nonneg
    intro i hi
    simp
    apply a_nonneg

lemma sum_div_two {a : ℕ → ℝ} (a_nonneg : 0 ≤ a) (h : p ≤ q) : ∑ n ∈ Icc p q, a (n / 2) ≤ ∑ i ∈ Icc (p / 2) (q / 2), a i * 2 := by
  have : Icc p q ⊆ Icc (2*(p/2)) (2*(q/2)+1)
  · intro n hn
    simp
    grind
  grw [sum_le_sum_of_subset_of_nonneg this (by intros; apply a_nonneg)]
  clear this
  have h2 : p/2 ≤ q/2
  · omega
  clear h
  generalize p/2 = p' at *
  generalize q/2 = q' at *
  induction q', h2 using Nat.le_induction with
  | base =>
    rw [sum_Icc_succ_top (by simp)]
    simp
    grind
  | succ q hmn ih =>
    simp [mul_add]
    grw [sum_Icc_succ_top (by grind), sum_Icc_succ_top (by grind), ih, sum_Icc_succ_top (by grind)]
    rw [add_assoc]
    simp

    rw [show (2*q + 1 + 1)/2 = q + 1 by grind]
    rw [show (2*q + 2 + 1)/2 = q + 1 by grind]
    rw [mul_two]

theorem summable_div_two (a_nonneg : 0 ≤ a) (h : Summable' a) : Summable' (fun n => a (n / 2)) := by
  rw [summable_iff_tail_decay] at h ⊢
  intro ε hε
  specialize h (ε / 2) (div_pos hε (by simp))
  obtain ⟨N, h⟩ := h
  refine ⟨2 * N, ?_⟩
  intro p hp q hq
  specialize h (p / 2) ?_ (q / 2) ?_
  · grw [hp]
    rw [mul_div_cancel_left₀]
    grind
  · grw [hq]
    grind
  rw [abs_of_nonneg] at h ⊢
  · rw [lt_div_iff₀ (by simp), sum_mul] at h
    by_cases hpq : p ≤ q
    · grw [sum_div_two a_nonneg hpq]
      exact h
    · rw [not_le] at hpq
      simp [hpq, hε]
  · apply sum_nonneg
    intro i hi
    apply a_nonneg
  · apply sum_nonneg
    intro i hi
    apply a_nonneg

/-
The other direction is pretty much the same proof but we apply the trick of duplicating each element in the series with `fun n => a (n / 2)`

Start with `have h := summable_grouped hφ (summable_div_two a_nonneg h)`
-/
theorem summable_condensed (a_nonneg : 0 ≤ a) (a_anti : Antitone a) (h : Summable' a) : Summable' (fun n => 2^n * a (2^n)) := by
  let φ n := 2^n
  have hφ : StrictMono φ
  · apply strictMono_nat_of_lt_succ
    grind

  have h := summable_grouped hφ (summable_div_two a_nonneg h)

  rw [summable_iff_tail_decay] at h ⊢
  intro ε hε
  specialize h ε hε
  obtain ⟨N, h⟩ := h
  refine ⟨N, ?_⟩
  intro p hp q hq
  specialize h p hp q hq

  rw [abs_of_nonneg] at h ⊢
  · apply lt_of_lt_of_le' h
    apply sum_le_sum
    intro i hi

    have : 2^i * a (2^i) = ∑ k ∈ Ico (φ i) (φ (i + 1)), a (2^i)
    · simp [φ]
      exact_mod_cast by grind
    rw [this]

    apply sum_le_sum
    intro j hj
    apply a_anti
    grind
  · apply sum_nonneg
    intro i hi
    simp
    apply a_nonneg
  · apply sum_nonneg
    intro i hi
    apply sum_nonneg
    intro j hj
    apply a_nonneg


theorem summable_iff_condensed (a_nonneg : 0 ≤ a) (a_anti : Antitone a) : Summable' a ↔ Summable' (fun n => 2^n * a (2^n)) := by
  exact ⟨summable_condensed a_nonneg a_anti, summable_of_condensed a_nonneg a_anti⟩

/-
Prove that the alternating series is not absolutely convergent using the condensation test
-/
theorem example_7_2_13.b' : ¬ Summable' |s| := by
  intro hf
  rw [summable_iff_condensed] at hf
  · have h := decay_of_summable hf
    rw [Metric.tendsto_atTop] at h
    specialize h (1/2) (by linarith)
    obtain ⟨N, h⟩ := h
    specialize h N le_rfl
    unfold s at h
    simp [abs_div] at h
    rw [← div_eq_mul_inv, inv_eq_one_div] at h
    rw [div_lt_div_iff₀, one_mul] at h
    · rw [abs_of_nonneg (by exact_mod_cast by simp)] at h
      have : (2:ℝ)^N + 1 ≤ 2^N * 2
      · exact_mod_cast by simp
      linarith
    · exact_mod_cast by simp
    · simp
  · exact abs_nonneg _
  · intro a b hab
    simp [s, abs_div]
    rw [inv_le_inv₀ (by exact_mod_cast by simp) (by exact_mod_cast by simp)]
    exact_mod_cast by linarith

lemma partials_add : partials (s + t) n = partials s n + partials t n := by
  simp [partials_def, sum_add_distrib]

theorem hasSum_add (hs : HasSum' s a) (ht : HasSum' t b) : HasSum' (s + t) (a + b) := by
  unfold HasSum'
  change Tendsto (fun _ => _) _ _
  simp_rw [partials_add]
  exact Tendsto.add hs ht

theorem summable_add (hs : Summable' s) (ht : Summable' t) : Summable' (s + t) := by
  obtain ⟨a, hs⟩ := hs
  obtain ⟨b, ht⟩ := ht
  exact ⟨a + b, hasSum_add hs ht⟩

#check tendsto_le_of_eventuallyLE

#check tendsto_pow_atTop_nhds_zero_iff

/-
Cauchy product
-/
#check tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm

/-
TODO explain ∑'[L] etc
-/

#check SummationFilter.conditional
#check SummationFilter.unconditional


-- TODO how to use tendsto_of_le_liminf_of_limsup_le and le_liminf_of_le
