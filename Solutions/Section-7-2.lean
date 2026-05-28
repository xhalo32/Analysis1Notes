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
4. Cauchy condensation test (optional). This is not in Tao's material (in section 7-2), but I found it a fun exercise. In the book this is in the next section.
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

Summation filters come in multiple varieties, two of which are of interest to us

- `unconditional`
- `conditional`

The statement `HasSum s L ↔ HasSum' s L` is not true because `HasSum` defaults to `unconditional`.
When using `conditional ℕ`, it coincides with our `HasSum'` as proved in `hasSum_iff_hasSum'`.

mathlib has very little API for conditional summation.

Here are some bits from the documentation that is helpful to get the picture.
Notice that `L` refers to a `SummationFilter`.

From the documentation of `HasSum`:

  By default `L` is the `unconditional` one, corresponding to the limit of all finite sets towards the entire type. So we take the sum over bigger and bigger finite sets. This sum operation is invariant under permuting the terms (while sums for more general summation filters usually are not).

Documentation of `SummationFilter.unconditional`:

  **Unconditional summation**: a function on `β` is said to be *unconditionally summable* if its partial sums over finite subsets converge with respect to the `atTop` filter.

Documentation of `SummationFilter.unconditional`:

  **Conditional summation**, for ordered types `β` such that closed intervals `[x, y]` are finite: this corresponds to limits of finite sums over larger and larger intervals.

Documentation of `SummationFilter.conditional_filter_eq_map_range`:

  Conditional summation over `ℕ` is given by limits of sums over `Finset.range n` as `n → ∞`.
-/

#check HasSum
#check SummationFilter.conditional_filter_eq_map_range

@[expose]
public section

open Finset Filter Topology SummationFilter

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

/-
## Cauchy product

https://en.wikipedia.org/wiki/Cauchy_product
-/
#check tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
