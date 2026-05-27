module

public import Solutions.«Section-7-2-infinite-series».Lemmas
public import Solutions.«Section-7-2-infinite-series».«1-Convergence»

@[expose]
public section alternating_series

open Finset Filter Topology

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

Note: `even` needs to start at zero otherwise it includes partials 0 = a₀, so the definition is `let even (n) := if n = 0 then 0 else S (2*((n - 1)/2) + 1)`

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

-- `example_7_2_13.b` etc are in the next file
