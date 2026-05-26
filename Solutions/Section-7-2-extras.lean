import Mathlib.Tactic
import Solutions.«Section-7-2»

open Finset Filter Topology

/-
This was my first proof of the alternating series test.

Because the indices run "twice as fast" this leads to a complication later where we need to divide by two.
-/
theorem _summable_alternating_of_antitone {a : ℕ → ℝ} (a_nonneg : 0 ≤ a) (a_antitone : Antitone a) (a_tendsto_zero : Tendsto a atTop (𝓝 0))
    : Summable' (fun n => (-1)^n * a n) := by
  rw [summable_partialsIcc]
  have odd_mono : Monotone fun m => partialsIcc (fun n => (-1)^n * a n) (2*m + 1)
  · apply monotone_nat_of_le_succ
    intro N
    simp [partialsIcc_def, mul_add, show 2 * N + 2 + 1 = 2 * N + 1 + 1 + 1 by simp]
    nth_rw 2 [sum_Icc_succ_top (by simp), sum_Icc_succ_top (by simp)]
    rw [Even.neg_one_pow (by grind), Odd.neg_one_pow (by grind)]
    have : a (2 * N + 2 + 1) ≤ a (2 * N + 2)
    · apply a_antitone
      simp
    linarith

  have even_anti : Antitone fun m => partialsIcc (fun n => (-1)^n * a n) (2*m)
  · apply antitone_nat_of_succ_le
    intro N
    simp [partialsIcc_def, mul_add, show 2 * N + 2 = 2 * N + 1 + 1 by simp]
    rw [sum_Icc_succ_top (by simp), sum_Icc_succ_top (by simp)]
    rw [Odd.neg_one_pow (by grind), Even.neg_one_pow (by grind)]
    have : a (2 * N + 2) ≤ a (2 * N + 1)
    · apply a_antitone
      simp
    linarith

  have partialsIcc_one_le_odd {m} : partialsIcc (fun n => (-1)^n * a n) 1 ≤ partialsIcc (fun n => (-1)^n * a n) (2 * m + 1)
  · rw [show 1 = 2 * 0 + 1 by simp]
    exact odd_mono (by simp)

  have odd_le_even {m} : partialsIcc (fun n => (-1)^n * a n) (2 * m + 1) ≤ partialsIcc (fun n => (-1)^n * a n) (2 * m)
  · rw [partialsIcc_def, sum_Icc_succ_top (by simp), partialsIcc_def]
    rw [Odd.neg_one_pow (by grind)]
    simp
    apply a_nonneg

  -- a 0 - a 1 is a lower bound of the antitone "even sequence"
  have lim_even := tendsto_atTop_ciInf even_anti (by
    rw [bddBelow_def]
    use partialsIcc (fun n => (-1)^n * a n) 1
    intro y hy
    simp at hy
    obtain ⟨x, rfl⟩ := hy
    grw [partialsIcc_one_le_odd, odd_le_even]
  )

  set L := ⨅ i, partialsIcc (fun n => (-1)^n * a n) (2 * i)

  -- difference goes to zero by s_tendsto_zero
  have lim_odd : Tendsto (fun m => partialsIcc (fun n => (-1)^n * a n) (2*m + 1)) atTop (𝓝 L)
  · apply Tendsto.congr_dist lim_even
    simp_rw [dist_partialsIcc_eq a_nonneg]
    apply Tendsto.comp a_tendsto_zero
    rw [tendsto_atTop_atTop_iff_of_monotone]
    · intro b
      use b
      omega
    · intro x y h
      simp [h]

  use L

  have lim_even' : Tendsto ((fun m => partialsIcc (fun n => (-1)^n * a n) (2*m)) ∘ fun m => m / 2) atTop (𝓝 L)
  · apply Tendsto.comp (y := atTop) (x := atTop) lim_even (Nat.tendsto_div_const_atTop (by simp))

  have lim_odd' : Tendsto ((fun m => partialsIcc (fun n => (-1)^n * a n) (2*m + 1)) ∘ fun m => (m - 1) / 2) atTop (𝓝 L)
  · apply Tendsto.comp (y := atTop) (x := atTop) lim_odd
    apply Tendsto.comp (g := fun x => x / 2) (y := atTop)
    · exact Nat.tendsto_div_const_atTop (by simp)
    · exact tendsto_sub_atTop_nat 1

  apply Tendsto.squeeze lim_odd' lim_even'
  · intro n
    by_cases hn : Odd n
    · obtain ⟨n, rfl⟩ := hn
      simp
    · rw [Nat.not_odd_iff_even] at hn
      obtain ⟨n, rfl⟩ := hn
      simp
      have : (n + n - 1) / 2 ≤ n
      · omega
      have := odd_mono this
      simp only at this
      grw [this]
      rw [← two_mul]
      exact partialsIcc_even_succ_le a_nonneg

  · intro n
    by_cases hn : Odd n
    · obtain ⟨n, rfl⟩ := hn
      simp [show (2 * n + 1) / 2 = n by omega]
      have : n ≤ n + 1
      · omega
      have := even_anti this
      simp only at this
      grw [← this]
      simp [mul_add]
      exact partialsIcc_odd_le_succ a_nonneg
    · rw [Nat.not_odd_iff_even] at hn
      obtain ⟨n, rfl⟩ := hn
      simp +arith
