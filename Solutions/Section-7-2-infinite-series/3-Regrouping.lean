module

public import Solutions.«Section-7-2-infinite-series».Lemmas
public import Solutions.«Section-7-2-infinite-series».«1-Convergence»
public import Solutions.«Section-7-2-infinite-series».«2-Alternating-series-test»

@[expose]
public section regrouping

open Finset Filter Topology

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
