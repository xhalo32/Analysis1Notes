module

public import Mathlib.Tactic
public import Mathlib.Analysis.PSeries
public import Solutions.«Section-7-2»

/-!
This is adapted from https://teorth.github.io/analysis/Analysis/Section_7_3/

It's time to switch to using mathlib's API: `HasSum`, `Summable` etc.

Theorems that are also in mathlib are prefixed with an underscore.

I proved Cauchy condensation test in the previous part.
-/

@[expose]
public section

open Finset Filter Topology SummationFilter

variable {s : ℕ → ℝ} {L M r : ℝ}

#check hasSum_iff_tendsto_nat_of_nonneg
#check Summable.hasSum_iff_tendsto_nat
-- Surprisingly there is no version for `conditional`, let's prove it ourselves

theorem hasSum_conditional_iff_tendsto_nat : HasSum s L (conditional ℕ) ↔ Tendsto (fun n => ∑ k ∈ range n, s k) atTop (𝓝 L) := by
  rw [hasSum_iff_hasSum']
  rfl

section nonnegative

theorem sum_range_monotone_of_nonneg (h : 0 ≤ s) : Monotone fun n => ∑ k ∈ range n, s k := by
  apply monotone_nat_of_le_succ
  intro n
  simp [sum_range_succ]
  apply h

-- More general version of the above
#check sum_mono_set_of_nonneg

/-
Straight-forward application of the following lemmas:
- `HasSum.tsum_eq`
- `exists_nat_subset_range`
- `sum_mono_set_of_nonneg`
- `sum_range_monotone_of_nonneg`
- `Monotone.ge_of_tendsto`
- `HasSum.tendsto_sum_nat`
-/
theorem sum_le_tsum_of_nonneg (hs : 0 ≤ s) {S : Finset ℕ} (h : Summable s) : ∑ k ∈ S, s k ≤ ∑' k, s k := by
  obtain ⟨L, h⟩ := h
  rw [h.tsum_eq] at *
  obtain ⟨n, hn⟩ := exists_nat_subset_range S
  apply le_trans (sum_mono_set_of_nonneg hs hn)
  exact (sum_range_monotone_of_nonneg hs).ge_of_tendsto h.tendsto_sum_nat _

-- More general version from mathlib
#check Summable.sum_le_tsum

/-
Here we can use the more general unconditional summation filter due to nonnegativity.

Note: `(Set.range fun n => ∑ k ∈ range n, s k) = {∑ k ∈ range n, s k | n : ℕ}`

⇒-direction: `Summable.sum_le_tsum`
-/
theorem summable_iff_bddAbove_of_nonneg (hs : 0 ≤ s) : Summable s ↔ BddAbove (Set.range fun n => ∑ k ∈ range n, s k) := by
  constructor
  · intro h
    use ∑' i, s i
    intro x hx
    simp at hx
    obtain ⟨n, rfl⟩ := hx
    exact sum_le_tsum_of_nonneg hs h
  · intro h
    cases tendsto_atTop_of_monotone (sum_range_monotone_of_nonneg hs) with
    | inl h2 =>
      rw [bddAbove_def] at h
      obtain ⟨M, h⟩ := h
      obtain ⟨n, hn⟩ := (h2.eventually_gt_atTop M).exists
      specialize h (∑ k ∈ range n, s k) (by simp)
      linarith
    | inr h2 =>
      apply (exists_congr _).mp h2
      simp [hasSum_iff_tendsto_nat_of_nonneg hs]

lemma bddAbove_range_iff : BddAbove (Set.range fun n => ∑ k ∈ range n, s k) ↔ ∃ M, ∀ n, ∑ k ∈ range n, s k ≤ M := by
  rw [bddAbove_def]
  simp

/-
This is true in the other direction too (assuming summability)
-/
theorem tsum_le_of_partials_le (hs : 0 ≤ s) (h : ∀ n, ∑ k ∈ range n, s k ≤ M) : ∑' k, s k ≤ M := by
  obtain ⟨L, hL⟩ := (summable_iff_bddAbove_of_nonneg hs).mpr (bddAbove_range_iff.mpr ⟨M, h⟩)
  rw [hL.tsum_eq]
  exact le_of_tendsto' ((hasSum_iff_tendsto_nat_of_nonneg hs _).mp hL) h

theorem partials_le_of_tsum_le (hs : 0 ≤ s) (h_summable : Summable s) (h : ∑' k, s k ≤ M) : ∀ n, ∑ k ∈ range n, s k ≤ M := by
  intro n
  grw [← h]
  exact sum_le_tsum_of_nonneg hs h_summable

theorem tsum_le_iff_partials_le (hs : 0 ≤ s) (h_summable : Summable s) : ∑' k, s k ≤ M ↔ ∀ n, ∑ k ∈ range n, s k ≤ M := by
  exact ⟨partials_le_of_tsum_le hs h_summable, tsum_le_of_partials_le hs⟩

/-
Start by obtaining the tsum.

Hint: `apply ge_of_tendsto' h.tendsto_sum_nat`
-/
theorem _tsum_nonneg (hs : 0 ≤ s) (h : Summable s) : 0 ≤ ∑' k, s k := by
  obtain ⟨L, h⟩ := h
  rw [h.tsum_eq]
  apply ge_of_tendsto' h.tendsto_sum_nat
  intro n
  apply sum_nonneg
  intro k hk
  apply hs

/-
Start by showing `0 ≤ t`. Proceed with `summable_iff_bddAbove_of_nonneg` and utilize `sum_le_sum`.
-/
theorem summable_of_le (h : s ≤ t) (hs : 0 ≤ s) (t_summable : Summable t) : Summable s := by
  have ht : 0 ≤ t
  · grw [hs]
    exact h
  rw [summable_iff_bddAbove_of_nonneg hs]
  rw [summable_iff_bddAbove_of_nonneg ht] at t_summable
  rw [bddAbove_def] at *
  obtain ⟨M, hM⟩ := t_summable
  refine ⟨M, ?_⟩
  simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hM ⊢
  intro n
  grw [← hM n]
  apply sum_le_sum
  intro i hi
  apply h

theorem tsum_le_of_le (h : s ≤ t) (hs : 0 ≤ s) (t_summable : Summable t) : ∑' k, s k ≤ ∑' k, t k := by
  have ht : 0 ≤ t
  · grw [hs]
    exact h
  apply tsum_le_of_partials_le hs
  intro n
  grw [← sum_le_tsum_of_nonneg (S := range n) ht t_summable]
  apply sum_le_sum
  intro i hi
  apply h

theorem not_summable_of_ge (h : s ≤ t) (hs : 0 ≤ s) (s_diverges : ¬ Summable s) : ¬ Summable t := by
  exact (summable_of_le h hs).mt s_diverges

end nonnegative

section geometric

lemma partials_geometric (h : |r| < 1) {n} : ∑ k ∈ range n, r^k = (1 - r^n)/(1 - r) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [sum_range_succ]
    -- grind -- works
    rw [ih]
    calc (1 - r^n) / (1 - r) + r^n
      _ = (1 - r^n) / (1 - r) + r^n * (1 - r) / (1 - r) := by grind
      _ = (1 - r^n + r^n * (1 - r)) / (1 - r) := by grind
      _ = (1 - r^n + r^n - r^(n + 1)) / (1 - r) := by grind
      _ = (1 - r^(n + 1)) / (1 - r) := by grind

theorem hasSum_geometric_conditional (h : |r| < 1) : HasSum (fun n => r^n) (1/(1 - r)) (conditional ℕ) := by
  rw [hasSum_conditional_iff_tendsto_nat]
  simp_rw [partials_geometric h]
  apply Tendsto.div
  · nth_rw 2 [show (1 : ℝ) = 1 - 0 by simp]
    apply Tendsto.sub _ (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h)
    simp
  · simp
  · grind

theorem summable_geometric_conditional (h : |r| < 1) : Summable (fun n => r^n) (conditional ℕ) := by
  exact ⟨_, hasSum_geometric_conditional h⟩

theorem hasSum_abs_geometric_conditional (h : |r| < 1) : HasSum (fun n => |r^n|) (1/(1 - |r|)) (conditional ℕ) := by
  simp_rw [abs_pow]
  apply hasSum_geometric_conditional
  simpa

theorem not_summable_geometric_conditional (h : 1 ≤ |r|) : ¬ Summable (fun n => r^n) (conditional ℕ) := by
  intro hf
  have : Tendsto (fun n => r^n) atTop (𝓝 0) := by
    -- I couldn't find the mathlib API for this
    rw [summable_iff_summable'] at hf
    exact decay_of_summable hf

  have habs : Tendsto (fun n => |r|^n) atTop (𝓝 0)
  · simp_rw [← abs_pow]
    rw [show (0 : ℝ) = |0| by simp]
    exact Tendsto.abs this

  by_cases hr : |r| = 1
  · have : Tendsto (fun n => |r|^n) atTop (𝓝 1)
    · simp [hr]
    have := tendsto_nhds_unique habs this
    simp at this
  · have : Tendsto (fun n => |r|^n) atTop atTop
    · apply tendsto_pow_atTop_atTop_of_one_lt
      grind
    exact not_tendsto_atTop_of_tendsto_nhds habs this

theorem summable_geometric_conditional_iff : Summable (fun n => r^n) (conditional ℕ) ↔ |r| < 1 := by
  refine ⟨?_, summable_geometric_conditional⟩
  contrapose!
  exact not_summable_geometric_conditional

-- unconditional version
#check summable_geometric_of_abs_lt_one
#check summable_geometric_iff_norm_lt_one

end geometric

section pseries

/-
The division by zero is on purpose to make the calculation easier.

Start by rewriting `summable_condensed_iff_of_nonneg` and show `(2^k : ℝ) * (1 / (2^k)^p) = (2^(1 - p : ℤ))^k` for all `k : ℕ`.
Finally rewrite `summable_geometric_iff_norm_lt_one`
-/
theorem summable_pseries {p} : Summable (fun n : ℕ => (1 : ℝ) / n^p) ↔ 1 < p := by
  rw [← summable_condensed_iff_of_nonneg]
  · have {k} : (2^k : ℝ) * (1 / (2^k)^p) = (2^(1 - p : ℤ))^k
    · rw [zpow_sub₀ (by simp)]
      simp only [zpow_natCast]
      ring
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    simp_rw [this]
    rw [summable_geometric_iff_norm_lt_one]
    simp
  · simp
  · intro a b ha hab
    simp
    rw [inv_le_inv₀]
    · grw [hab]
    · apply pow_pos
      exact_mod_cast by linarith
    · exact_mod_cast pow_pos ha _

#check Real.summable_nat_rpow_inv

end pseries

/-
One final exercise involving `sum_le_tsum_of_nonneg`.
-/

theorem _hasSum_zero_iff_of_nonneg (hs : 0 ≤ s) : HasSum s 0 ↔ s = 0 := by
  constructor
  · intro h
    ext n
    simp
    suffices s n ≤ 0 by
      have := hs n
      simp at this
      grind
    rw [← h.tsum_eq]
    grw [← sum_le_tsum_of_nonneg hs h.summable (S := {n})]
    simp
  · intro rfl
    rw [hasSum_iff_tendsto_nat_of_nonneg hs]
    simp

end
