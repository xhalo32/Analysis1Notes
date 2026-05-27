module

public import Solutions.«Section-7-2-infinite-series».Lemmas
public import Solutions.«Section-7-2-infinite-series».«1-Convergence»

@[expose]
public section

open Finset Filter Topology

/-
Telescoping series
-/
def telescope (a : ℕ → ℝ) (n : ℕ) := a n - a (n + 1)

theorem telescope_apply : telescope a n = a n - a (n + 1) := rfl

theorem partials_telescope : partials (telescope a) n = a 0 - a n := by
  induction n with
  | zero =>
    simp [partials_def, telescope_apply]
  | succ n ih =>
    simp [telescope_apply, ih]

theorem hasSum_telescope (a_tendsto_zero : Tendsto a atTop (𝓝 0)) : HasSum' (telescope a) (a 0) := by
  change Tendsto (fun _ => _) _ _
  simp_rw [partials_telescope]
  nth_rw 2 [show a 0 = a 0 - 0 by simp]
  apply Tendsto.sub _ a_tendsto_zero
  simp

theorem summable_telescope (a_tendsto_zero : Tendsto a atTop (𝓝 0)) : Summable' (telescope a) := by
  exact ⟨_, hasSum_telescope a_tendsto_zero⟩

theorem tendsto_of_hasSum_telescope (h : HasSum' (telescope a) L) : Tendsto a atTop (𝓝 (a 0 - L)) := by
  change Tendsto (fun _ => _) _ _ at *
  simp_rw [partials_telescope] at h
  have : Tendsto (fun n => a 0 - a n - a 0) atTop (𝓝 (L - a 0))
  · apply Tendsto.sub h
    simp
  have := this.neg
  simpa

/-
Approach: start with `rw [summable_shift_iff (m := 1)]`, and show that the series is telescoping

Hints:
1. `tendsto_one_div_add_atTop_nhds_zero_nat` or `tendsto_const_div_atTop_nhds_zero_nat` might be useful
-/
example : Summable' (fun n => 1 / (n * (n + 1))) := by
  rw [summable_shift_iff (m := 1)]
  have : shift 1 (fun n => 1 / (n * (n + 1))) = telescope (shift 1 (1 / ·))
  · ext n
    simp [shift_apply, telescope]
    grind
  rw [this]
  apply summable_telescope
  rw [tendsto_shift_atTop]
  exact tendsto_const_div_atTop_nhds_zero_nat 1

example : ¬ Summable' (fun n => (-1:ℝ)^n) := by
  have {n} : (-1:ℝ)^n = telescope (fun n => if Even n then 1 else 0) n
  · simp [telescope_apply]
    -- rw [Nat.even_add_one] -- doesn't work because if depends on `(n + 1).instDecidablePredEven`
    -- rw! (castMode := .all) [Nat.even_add_one]
    simp_rw [Nat.even_add_one]
    split
    next h =>
      simp [Even.neg_one_pow h]
    next h =>
      rw [Nat.not_even_iff_odd] at h
      simp [Odd.neg_one_pow h]
  simp_rw [this]

  intro ⟨L, h⟩
  apply tendsto_of_hasSum_telescope at h
  rw [Metric.tendsto_atTop] at h
  specialize h (1/2) (by linarith)
  obtain ⟨N, h⟩ := h
  have h1 := h (2 * N) (by linarith)
  have h2 := h (2 * N + 1) (by linarith)
  simp [Real.dist_eq] at h1 h2
  grind
