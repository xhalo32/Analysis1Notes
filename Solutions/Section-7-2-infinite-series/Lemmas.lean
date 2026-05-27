module
public import Mathlib.Tactic

@[expose]
public section

/-!
The purpose of this file is to cover some missing mathlib API
-/

namespace Finset

variable {ι α : Type*} {a a₁ a₂ b b₁ b₂ c x : α} [Preorder α] [LocallyFiniteOrder α]

@[simp]
theorem Ico_disjoint_Ico_of_le {d : α} (hbc : b ≤ c) : Disjoint (Ico a b) (Ico c d) :=
  disjoint_left.2 fun _ h1 h2 ↦ not_and_of_not_left _
    (by grind) (mem_Ico.1 h2)

end Finset

lemma Nat.le_pow_self (n : ℕ) : n ≤ 2 ^ n := by
  induction n with grind
  -- Manual proof
  -- induction n with
  -- | zero =>
  --   simp
  -- | succ n ih =>
  --   rw [Nat.two_pow_succ]
  --   apply add_le_add ih
  --   exact Nat.one_le_two_pow

open Finset in
/--
`sum_of_nonempty` from section 7-1 in suitable generality
-/
theorem sum_of_empty [Preorder α] [LocallyFiniteOrder α] [AddCommMonoid β] {n m : α} (h : n < m) (a : α → β) : ∑ i ∈ Icc m n, a i = 0 := by
  rw [Icc_eq_empty_iff.mpr (by grind)]
  exact sum_empty
