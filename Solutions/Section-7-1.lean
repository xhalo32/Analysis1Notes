import Mathlib.Tactic

/-!
## 7.1. Finite series

Source: https://teorth.github.io/analysis/Analysis/Section_7_1/
-/

open BigOperators Finset

section

theorem sum_of_empty {n m:ℤ} (h: n < m) (a: ℤ → ℝ) : ∑ i ∈ Icc m n, a i = 0 := by
  rw [sum_eq_zero]; intro _; rw [mem_Icc]; grind

theorem sum_of_nonempty {n m:ℤ} (h: n ≥ m-1) (a: ℤ → ℝ) :
    ∑ i ∈ Icc m (n+1), a i = ∑ i ∈ Icc m n, a i + a (n+1) := by
  rw [add_comm _ (a (n+1))]
  convert sum_insert _
  . ext; simp; omega
  . infer_instance
  simp

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-2), a i = 0 := by
  rw [Icc_eq_empty_of_lt]
  · simp
  · simp

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-1), a i = 0 := by
  simp

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m m, a i = a m := by
  rw [sum_eq_single_of_mem m]
  · simp
  · simp

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+1), a i = a m + a (m+1) := by
  convert sum_insert _ (s := {m + 1})
  · grind
  · simp
  · simp

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+2), a i = a m + a (m+1) + a (m+2) := by
  have : Icc m (m + 2) = {m, m+1, m+2}
  · grind
  rw [this]
  simp
  ring

theorem concat_finite_series {m n p:ℤ} (hmn: m ≤ n+1) (hpn : n ≤ p) (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc (n+1) p, a i = ∑ i ∈ Icc m p, a i := by
  induction p, hpn using Int.le_induction with
  | base =>
    nth_rw 2 [sum_of_empty] <;> simp
  | succ p hmn ih =>
    rw [sum_of_nonempty, ← add_assoc, ih, sum_of_nonempty] <;> grind

theorem shift_finite_series {m n k:ℤ} (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i = ∑ i ∈ Icc (m+k) (n+k), a (i-k) := by
  by_cases hmn : m ≤ n
  · induction n, hmn using Int.le_induction with
    | base =>
      simp
    | succ n hmn ih =>
      rw [show ∀ k, n + 1 + k = n + k + 1 by simp +arith]
      rw [sum_of_nonempty, ih, sum_of_nonempty] <;> grind
  · rw [sum_of_empty, sum_of_empty] <;> grind

theorem finite_series_add {m n:ℤ} (a b: ℤ → ℝ) :
  ∑ i ∈ Icc m n, (a i + b i) = ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc m n, b i := by
  by_cases hmn : m ≤ n
  · induction n, hmn using Int.le_induction with
    | base =>
      simp
    | succ n hmn ih =>
      calc ∑ i ∈ Icc m (n + 1), (a i + b i)
      _ = (∑ i ∈ Icc m n, (a i + b i)) + (a (n + 1) + b (n + 1)) := by rw [sum_of_nonempty (by grind)]
      _ = (∑ i ∈ Icc m n, a i) + (∑ i ∈ Icc m n, b i) + (a (n + 1) + b (n + 1)) := by rw [ih]
      _ = ((∑ i ∈ Icc m n, a i) + a (n + 1)) + ((∑ i ∈ Icc m n, b i) + b (n + 1)) := by ring
      _ = ∑ i ∈ Icc m (n + 1), a i + ∑ i ∈ Icc m (n + 1), b i := by
          rw [← sum_of_nonempty (by grind), ← sum_of_nonempty (by grind)]
  · rw [sum_of_empty, sum_of_empty, sum_of_empty] <;> grind

theorem finite_series_const_mul {m n:ℤ} (a: ℤ → ℝ) (c:ℝ) :
  ∑ i ∈ Icc m n, c * a i = c * ∑ i ∈ Icc m n, a i := by
  by_cases hmn : m ≤ n
  · induction n, hmn using Int.le_induction with
  | base =>
    simp
  | succ n hmn ih =>
    rw [sum_of_nonempty (by grind), ih, ← mul_add, ← sum_of_nonempty (by grind)]
  · rw [sum_of_empty, sum_of_empty, mul_zero] <;> grind

theorem abs_finite_series_le {m n:ℤ} (a: ℤ → ℝ) :
  |∑ i ∈ Icc m n, a i| ≤ ∑ i ∈ Icc m n, |a i| := by
  sorry

theorem finite_series_of_le {m n:ℤ}  {a b: ℤ → ℝ} (h: ∀ i, m ≤ i → i ≤ n → a i ≤ b i) :
  ∑ i ∈ Icc m n, a i ≤ ∑ i ∈ Icc m n, b i := by
  sorry

theorem finite_series_of_rearrange {n:ℕ} {X':Type*} (X: Finset X') (hcard: X.card = n)
  (f: X' → ℝ) (g h: ℤ → X) (hg: Function.Bijective ((Icc (1:ℤ) n).restrict g)) (hh: Function.Bijective ((Icc (1:ℤ) n).restrict h)) :
    ∑ i ∈ Icc (1:ℤ) n, f (g i) = ∑ i ∈ Icc (1:ℤ) n, f (h i) := by
  sorry

theorem finite_series_of_empty {X':Type*} (f: X' → ℝ) : ∑ i ∈ ∅, f i = 0 := by
  sorry

theorem finite_series_of_singleton {X':Type*} (f: X' → ℝ) (x₀:X') : ∑ i ∈ {x₀}, f i = f x₀ := by
  sorry

theorem map_finite_series {X:Type*} [Fintype X] [Fintype Y] (f: X → ℝ) {g:Y → X}
  (hg: Function.Bijective g) :
    ∑ x, f x = ∑ y, f (g y) := by
  sorry

open Classical in
theorem finite_series_of_disjoint_union {Z:Type*} {X Y: Finset Z} (hdisj: Disjoint X Y) (f: Z → ℝ) :
    ∑ z ∈ X ∪ Y, f z = ∑ z ∈ X, f z + ∑ z ∈ Y, f z := by
  sorry

theorem finite_series_of_add {X':Type*} (f g: X' → ℝ) (X: Finset X') :
    ∑ x ∈ X, (f + g) x = ∑ x ∈ X, f x + ∑ x ∈ X, g x := by
  sorry

theorem finite_series_of_const_mul {X':Type*} (f: X' → ℝ) (X: Finset X') (c:ℝ) :
    ∑ x ∈ X, c * f x = c * ∑ x ∈ X, f x := by
  sorry

theorem finite_series_of_le' {X':Type*} (f g: X' → ℝ) (X: Finset X') (h: ∀ x ∈ X, f x ≤ g x) :
    ∑ x ∈ X, f x ≤ ∑ x ∈ X, g x := by
  sorry

theorem abs_finite_series_le' {X':Type*} (f: X' → ℝ) (X: Finset X') :
    |∑ x ∈ X, f x| ≤ ∑ x ∈ X, |f x| := by
  sorry

theorem finite_series_of_finite_series {XX YY:Type*} (X: Finset XX) (Y: Finset YY)
  (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ z ∈ X.product Y, f z := by
  sorry

end

section

theorem binomial_theorem (x y:ℝ) (n:ℕ) :
    (x + y)^n
    = ∑ j ∈ Icc (0:ℤ) n,
    n.factorial / (j.toNat.factorial * (n-j).toNat.factorial) * x^j * y^(n - j) := by
  sorry

theorem lim_of_finite_series {X:Type*} [Fintype X] (a: X → ℕ → ℝ) (L : X → ℝ)
  (h: ∀ x, Filter.atTop.Tendsto (a x) (nhds (L x))) :
    Filter.atTop.Tendsto (fun n ↦ ∑ x, a x n) (nhds (∑ x, L x)) := by
  sorry

theorem sum_union_disjoint {n : ℕ} {S : Type*} [Fintype S]
    (E : Fin n → Finset S)
    (disj : ∀ i j : Fin n, i ≠ j → Disjoint (E i) (E j))
    (cover : ∀ s : S, ∃ i, s ∈ E i)
    (f : S → ℝ) :
    ∑ s, f s = ∑ i, ∑ s ∈ E i, f s := by
  sorry

theorem sum_finite_col_row_counts {n m : ℕ} (a : Fin n → Fin m) :
    ∑ i, (a i : ℕ) = ∑ j : Fin m, {i : Fin n | j < a i}.toFinset.card := by
  sorry

end
