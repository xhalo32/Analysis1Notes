module

public import Solutions.«Section-7-2-infinite-series».Lemmas
public import Mathlib.Tactic

open Finset Filter Topology

@[expose]
public section definitions

/--
The sequence `S` of partial sums of `s`: `S (n + 1) = s 0 + ··· + s n`.
-/
def partials (s : ℕ → ℝ) (N:ℕ) : ℝ := ∑ n ∈ range N, s n

lemma partials_def : partials s N = ∑ n ∈ range N, s n := rfl

@[simp]
theorem partials_succ (s : ℕ → ℝ) {N:ℕ} : partials s (N + 1) = partials s N + s N := by
  rw [partials_def, sum_range_succ]
  rfl

/-
An alternative definition using Icc
-/
def partialsIcc (s : ℕ → ℝ) (N:ℕ) : ℝ := ∑ n ∈ Icc 0 N, s n

lemma partialsIcc_def : partialsIcc s N = ∑ n ∈ Icc 0 N, s n := rfl

def HasSum' (s : ℕ → ℝ) (L : ℝ) := Tendsto (partials s) atTop (𝓝 L)

def Summable' (s : ℕ → ℝ) := ∃ L, HasSum' s L


/-
Equivalent definition of convergence using partialsIcc.

The proof is a direct consequence of `tendsto_add_atTop_iff_nat`
-/
theorem hasSum_partialsIcc : HasSum' s L ↔ Tendsto (partialsIcc s) atTop (𝓝 L) := by
  change Tendsto (fun _ => _) _ _ ↔ Tendsto (fun _ => _) _ _
  simp_rw [partialsIcc_def, partials_def, range_eq_Ico]
  rw [← tendsto_add_atTop_iff_nat (k := 1)]
  simp [Ico_add_one_right_eq_Icc]

theorem summable_partialsIcc : Summable' s ↔ ∃ L, Tendsto (partialsIcc s) atTop (𝓝 L) := by
  simp_rw [← hasSum_partialsIcc]
  rfl

open Classical in
noncomputable def tsum' (s : ℕ → ℝ) : ℝ := if h : Summable' s then h.choose else 0

lemma tsum_summable (h : Summable' s) : tsum' s = h.choose := by
  unfold tsum'
  grind

lemma summable_spec (h : Summable' s) : Tendsto (partials s) atTop (𝓝 h.choose) := Exists.choose_spec h

lemma partials_tendsto_of_summable (h : Summable' s) : Tendsto (partials s) atTop (𝓝 (tsum' s)) := by
  rw [tsum_summable h]
  exact Exists.choose_spec h

theorem summable_of_hasSum (h : HasSum' s L) : Summable' s := by
  use L

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

lemma sum_Ico_eq_partials_sub {s : ℕ → ℝ} {p q} (hpq : p ≤ q) : ∑ n ∈ Ico p q, s n = partials s q - partials s p := by
  induction q, hpq using Nat.le_induction with
  | base =>
    simp
  | succ q hpq ih =>
    rw [sum_Ico_succ_top hpq, ih]
    simp
    ring

lemma sum_Ioc_eq_partialsIcc_sub {s : ℕ → ℝ} {p q} (hpq : p ≤ q) : ∑ n ∈ Ioc p q, s n = partialsIcc s q - partialsIcc s p := by
  induction q, hpq using Nat.le_induction with
  | base =>
    simp
  | succ q hpq ih =>
    rw [sum_Ioc_succ_top hpq, ih]
    simp [partialsIcc_def, sum_Icc_succ_top]
    ring

end definitions

public section cauchy_criterion

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

/-
This is a consequence of `summable_iff_tail_decay` when specialized with `p = q`.
-/
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

end cauchy_criterion

public section absolute_convergence

/-
The absolute value of a function is simply taken pointwise.

I don't see a reason to define absolute convergence separately.
-/
example {s : ℕ → ℝ} : |s| = fun n => |s n| := rfl

@[expose]
def CondSummable (s : ℕ → ℝ) := Summable' s ∧ ¬ Summable' |s|

lemma abs_sum_abs_eq {a : ℕ → ℝ} : |∑ n ∈ s, abs (a n)| = ∑ n ∈ s, |a n| := by
  rw [abs_eq_self]
  apply sum_nonneg
  simp

/-
You might need `Pi.abs_apply`

Hints:
1. Start with rewriting `summable_iff_tail_decay` and `abs_sum_le_sum_abs`
-/
theorem summable_of_abs_summable (h : Summable' |s|) : Summable' s := by
  rw [summable_iff_tail_decay] at h ⊢
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

end absolute_convergence

public section series_laws

/-
Start with `change Tendsto (fun _ => _) _ _` to unfold so that `partials` is fully applied.

Hints:
1. `mul_sum` and `Tendsto.const_mul`
-/
theorem hasSum_const_mul_left {a} (h : HasSum' a L) : HasSum' (fun n => c * a n) (c * L) := by
  change Tendsto (fun _ => _) _ _
  simp_rw [partials_def, ← mul_sum]
  exact Tendsto.const_mul _ h

theorem summable_const_mul_left {a} (h : Summable' a) : Summable' (fun n => c * a n) := by
  obtain ⟨L, h⟩ := h
  use c * L
  exact hasSum_const_mul_left h

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

lemma partials_neg : partials (-s) n = - partials s n := by
  simp [partials_def]

theorem hasSum_neg (hs : HasSum' s a) : HasSum' (- s) (- a) := by
  change Tendsto (fun _ => _) _ _
  simp_rw [partials_neg]
  exact Tendsto.neg hs

theorem hasSum_sub (hs : HasSum' s a) (ht : HasSum' t b) : HasSum' (s - t) (a - b) := by
  simp [sub_eq_add_neg]
  exact hasSum_add hs (hasSum_neg ht)

end series_laws

@[expose]
public section shifting

def shift (m : ℕ) (s : ℕ → ℝ) (n : ℕ) := s (n + m)

lemma shift_def : shift m s = fun n : ℕ => s (n + m) := rfl

lemma shift_def' : shift m s = s ∘ (· + m) := rfl

lemma shift_apply : shift m s n = s (n + m) := rfl

@[simp]
lemma shift_zero : shift 0 s = s := rfl

def tail (s : ℕ → ℝ) := shift 1 s

theorem partials_tail : s 0 + partials (tail s) n = partials s (n + 1) := by
  simp [partials_def, tail, shift_apply]
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, ← add_assoc, ih]

/-
`tendsto_add_atTop_iff_nat` is useful in the following two theorems
-/
theorem hasSum_tail (h : HasSum' s L) : HasSum' (tail s) (L - s 0) := by
  change Tendsto (fun n => _) _ _
  conv =>
    enter [1, n]
    rw [show partials (tail s) n = s 0 + partials (tail s) n - s 0 by simp]
  apply Tendsto.sub
  · simp_rw [partials_tail]
    exact (tendsto_add_atTop_iff_nat 1).mpr h
  · rw [tendsto_const_nhds_iff]

theorem hasSum_of_hasSum_tail (h : HasSum' (tail s) (L - s 0)) : HasSum' s L := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  change Tendsto (fun n => _) _ _
  simp_rw [← partials_tail]
  rw [show L = s 0 + (L - s 0) by simp]
  apply Tendsto.add _ h
  rw [tendsto_const_nhds_iff]

theorem hasSum_tail_iff : HasSum' s L ↔ HasSum' (tail s) (L - s 0) := by
  refine ⟨hasSum_tail, hasSum_of_hasSum_tail⟩

theorem shift_succ_eq_tail_shift : shift (m + 1) s = tail ((shift m) s) := by
  simp +arith [shift_def, tail]

/-
This is doable with induction in `m` where the induction step utilizes `hasSum_tail`.

Hints:
1. Start the induction step with `simp_rw [shift_succ_eq_tail_shift, sum_range_succ]`
2. Utilize the fact that `s m = shift m s 0`
3. To finish, use `rw [← hasSum_tail_iff]` and `ih`
-/
theorem hasSum_shift_iff {m : ℕ} : HasSum' s L ↔ HasSum' (shift m s) (L - ∑ k ∈ range m, s k) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    simp_rw [shift_succ_eq_tail_shift, sum_range_succ, ← sub_sub]
    rw [show s m = shift m s 0 by simp [shift_apply]]
    rw [← hasSum_tail_iff]
    exact ih

theorem hasSum_shift_iff' {m : ℕ} (hm : M = L - ∑ k ∈ range m, s k) : HasSum' s L ↔ HasSum' (shift m s) M := by
  rw [hm]
  exact hasSum_shift_iff

theorem summable_shift_iff : Summable' s ↔ Summable' (shift m s) := by
  constructor
  · intro ⟨L, h⟩
    exact ⟨_, hasSum_shift_iff.mp h⟩
  · intro ⟨L, h⟩
    refine ⟨L + ∑ k ∈ range m, s k, ?_⟩
    apply (hasSum_shift_iff' _).mpr h
    simp

/-
This is `tendsto_add_atTop_iff_nat` exactly
-/
theorem tendsto_shift_atTop : Tendsto (shift m s) atTop (𝓝 L) ↔ Tendsto s atTop (𝓝 L) := by
  exact tendsto_add_atTop_iff_nat _


end shifting


section examples

/-
Here are some examples of converging and diverging series
-/

theorem example_7_2_4.a (N:ℕ) : partials (fun n ↦ (2:ℝ)^(-(n + 1):ℤ)) N = 1 - (2:ℝ)^(-(N : ℤ)) := by
  rw [partials_def]
  induction N with
  | zero =>
    norm_num
  | succ n ih =>
    rw [sum_range_succ, ih]
    norm_cast
    simp
    ring

theorem example_7_2_4.b : HasSum' (fun n ↦ (2:ℝ)^(-(n + 1):ℤ)) 1 := by
  unfold HasSum'
  rw [funext example_7_2_4.a]
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

theorem example_7_2_4.c : tsum' (fun n ↦ (2:ℝ)^(-(n + 1):ℤ)) = 1 := by
  exact tsum_eq_of_hasSum example_7_2_4.b

theorem example_7_2_4'.a {N:ℕ} : partials (fun n ↦ (2:ℝ)^(n:ℤ)) N = (2:ℝ)^N - 1 := by
  rw [partials_def]
  induction N with
  | zero =>
    norm_num
  | succ n ih =>
    rw [sum_range_succ, ih]
    norm_cast
    grind

theorem example_7_2_4'.b : ¬ Summable' (fun n ↦ (2:ℝ)^(n:ℤ)) := by
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

/-
Examples involving `diverges_of_nodecay`
-/

theorem example_7_2_7 : ¬ Summable' (fun _ ↦ 1) := by
  apply diverges_of_nodecay
  simp

/-
Note: if you use `simp`, make sure it's not using `tendsto_pow_atTop_nhds_zero_iff` as we haven't proved that.
-/
theorem example_7_2_7' : ¬ Summable' (fun n:ℕ ↦ (-1:ℝ)^n) := by
  apply diverges_of_nodecay
  -- simp -- would use tendsto_pow_atTop_nhds_zero_iff, which we haven't proved
  intro h
  rw [Metric.tendsto_atTop] at h
  specialize h (1/2) (by grind)
  obtain ⟨N, h⟩ := h
  specialize h N le_rfl
  norm_num at h

end examples
