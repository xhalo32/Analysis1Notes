module

public import Solutions.«Section-7-2-infinite-series».Lemmas
public import Solutions.«Section-7-2-infinite-series».«1-Convergence»
public import Solutions.«Section-7-2-infinite-series».«2-Alternating-series-test»
public import Solutions.«Section-7-2-infinite-series».«3-Regrouping»
public import Solutions.«Section-7-2-infinite-series».«4-Condensation»
public import Solutions.«Section-7-2-infinite-series».«5-Telescope»

/-!
# 7.2. Infinite series

Source: https://teorth.github.io/analysis/Analysis/Section_7_2/.

As before, I will reformulate the exercises to match definitions that are closer to mathlib and easier to work with.

We immediately diverge from the material and define a series as a sequence `ℕ → ℝ`.

The chapter is also split into subchapters as the solutions file would otherwise reach > 1000 lines:
1. Convergence: definition of partial sums, convergence of series (i.e. summability), absolute convergence, series laws
2. Alternating series test. This deserves its own file
3. Regrouping terms to form a new series
4. Cauchy condensation test (optional). This is not in Tao's material, but I found it a fun exercise.
5. Telescoping series (optional).

The series laws have been placed into 1-Convergence due to their simplicity.
-/

/-
These are mathlib names of some relevant results from 7-1
-/
#check Finset.sum_Icc_succ_top -- sum_of_nonempty
#check Finset.sum_Ico_consecutive -- concat_sum
#check Finset.sum_Ico_add_right_sub_eq -- shift_sum
#check Finset.abs_sum_le_sum_abs -- abs_sum_le_sum_abs_Icc

/-
This is glue between Ico and Icc
-/
#check Finset.sum_Ico_add_eq_sum_Icc

/-
`range N` is `Ico 0 N`
-/
#check Finset.range_eq_Ico

/-
Let's connect the definitions and results with mathlib.

First we need to learn about the `SummationFilter`.

## Summation filters

TODO

- `unconditional`
- `conditional`
-/

#check HasSum

/-
Not true because we need the conditional summation filter from the documentation of `HasSum`:

By default `L` is the `unconditional` one, corresponding to the limit of all finite sets towards
the entire type. So we take the sum over bigger and bigger finite sets. This sum operation is
invariant under permuting the terms (while sums for more general summation filters usually are not).
-/
-- open Finset in
-- theorem hasSum_iff_hasSum'_bad : HasSum s L ↔ HasSum' s L := by
--   constructor
--   · intro h
--     have := summable_norm_iff.mpr h.summable
--     rw [hasSum_iff_tendsto_nat_of_summable_norm this] at h
--     exact h
--   · intro h
--     unfold HasSum
--     simp [SummationFilter.unconditional]
--     unfold HasSum' at h
--     rw [Metric.tendsto_atTop] at *
--     intro ε hε
--     specialize h ε hε
--     obtain ⟨N, h⟩ := h
--     refine ⟨range N, ?_⟩
--     intro S hS
--     -- S can be pathological and choose elements from the series
--     by_cases hS2 : S.Nonempty
--     · specialize h (max N (S.max' hS2 + 1)) (by simp)
--       have : S ⊆ range (max N (S.max' hS2 + 1))
--       · rw [subset_range]
--         intro x hx
--         apply lt_max_of_lt_right
--         simp [le_max' S x hx]
--       sorry -- this is not possible without 0 ≤ s

open SummationFilter

theorem hasSum_iff_hasSum' : HasSum s L (conditional ℕ) ↔ HasSum' s L := by
  unfold HasSum
  -- The conditional summation filter is the standard partial sums over a range
  rw [SummationFilter.conditional_filter_eq_map_range]
  rfl

theorem summable_iff_summable' : Summable s (conditional ℕ) ↔ Summable' s := by
  unfold Summable Summable'
  simp_rw [hasSum_iff_hasSum']

/-
Other interesting API
-/

#check tendsto_le_of_eventuallyLE
#check tendsto_pow_atTop_nhds_zero_iff

/-
Cauchy product
-/
#check tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
