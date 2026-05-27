module

public import Solutions.«Section-7-2-infinite-series».Lemmas
public import Solutions.«Section-7-2-infinite-series».«1-Convergence»
public import Solutions.«Section-7-2-infinite-series».«2-Alternating-series-test»
public import Solutions.«Section-7-2-infinite-series».«3-Regrouping»

@[expose]
public section cauchy_condensation_test

open Finset Filter Topology

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
Prove that the alternating series in Example 7.2.13 is not absolutely convergent using the condensation test
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
