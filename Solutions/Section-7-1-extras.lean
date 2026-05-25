import Mathlib.Tactic
import Solutions.«Section-7-1»

open Finset

/-
This is concat_sum using induction explicitly in the difference between n and p
-/
theorem concat_sum' {m n p:ℤ} (hmn: m ≤ n+1) (hpn : n ≤ p) (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc (n+1) p, a i = ∑ i ∈ Icc m p, a i := by
  induction h : p - n generalizing n p with
  | zero =>
    have : n = p
    · grind
    subst this
    nth_rw 2 [sum_of_empty (by simp)]
    simp
  | pred k ih =>
    grind
  | succ k ih =>
    -- IH gives us that the equation holds until p - 1
    specialize @ih n (p - 1) ?_ ?_ ?_
    · grind
    · grind
    · grind

    rw [show p = p - 1 + 1 by simp]
    rw [sum_of_nonempty (by grind), ← add_assoc, ih, sum_of_nonempty (by grind)]

/-
This was my initial attempt at reformulating `finite_series_of_rearrange` without `π` and translating the pre-filled proof.

Turns out that it is considerably easier to prove a "one-sided" variant with just one bijection first.
-/
example {n:ℕ} {X':Type*} (X: Finset X') (hcard: X.card = n) (f: X' → ℝ) (g h: ℤ → X')
  (hg1 : ∀ i ∈ Icc (1:ℤ) n, g i ∈ X)
  (hh1 : ∀ i ∈ Icc (1:ℤ) n, h i ∈ X)
  (g_bij: Function.Bijective (fun i : Icc (1:ℤ) n => (⟨_, hg1 _ i.prop⟩ : X)))
  (h_bij: Function.Bijective (fun i : Icc (1:ℤ) n => (⟨_, hh1 _ i.prop⟩ : X))) :
    ∑ i ∈ Icc (1:ℤ) n, f (g i) = ∑ i ∈ Icc (1:ℤ) n, f (h i) := by
  classical
  induction n generalizing X g h with
  | zero =>
    simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one]
    rw [sum_of_nonempty (by simp)]
    set x : X := ⟨g (n+1), hg1 _ (by simp)⟩
    have ⟨⟨j, hj'⟩, hj⟩ := h_bij.surjective x
    obtain ⟨hj1, hj2⟩ := mem_Icc.mp hj'
    let h' : ℤ → X' := fun i ↦ if (i:ℤ) < j then h i else h (i+1)

    have h1 : ∑ i ∈ Icc (j + 1) (n + 1), f (h i) = ∑ i ∈ Icc (j + 1) (n + 1), f (h' (i - 1))
    · -- We need to turn ↑ into a function composition for `sum_apply_ite_of_true`
      -- change _ = ∑ i ∈ _, (f ∘ Subtype.val) _
      rw [sum_apply_ite_of_false]
      · simp
      · grind

    have h2 : ∑ i ∈ Icc 1 (j - 1), f (h i) = ∑ i ∈ Icc 1 (j - 1), f (h' i)
    · -- change _ = ∑ i ∈ _, (f ∘ Subtype.val) _
      rw [sum_apply_ite_of_true]
      simp

    have h3 : ∑ i ∈ Icc (1:ℤ) (n + 1), f (h i) = ∑ i ∈ Icc (1:ℤ) n, f (h' i) + f x
    · calc
      _ = ∑ i ∈ Icc 1 j, f (h i) + ∑ i ∈ Icc (j + 1) (n + 1), f (h i) := by rw [concat_finite_series] <;> grind
      _ = ∑ i ∈ Icc 1 j, f (h i) + ∑ i ∈ Icc (j + 1) (n + 1), f (h' (i - 1)) := by rw [h1]
      _ = ∑ i ∈ Icc 1 j, f (h i) + ∑ i ∈ Icc j n, f (h' i) := by rw [shift_finite_series (n := n)]
      _ = ∑ i ∈ Icc 1 (j - 1 + 1), f (h i) + ∑ i ∈ Icc j n, f (h' i) := by simp
      _ = ∑ i ∈ Icc 1 (j - 1), f (h i) + ∑ i ∈ Icc j n, f (h' i) + f (h j) := by rw [sum_of_nonempty (by grind)]; grind
      _ = ∑ i ∈ Icc 1 (j - 1), f (h i) + ∑ i ∈ Icc j n, f (h' i) + f x := by simp [← hj]
      _ = ∑ i ∈ Icc 1 (j - 1), f (h' i) + ∑ i ∈ Icc j n, f (h' i) + f x := by rw [h2]
      _ = ∑ i ∈ Icc 1 (n : ℤ), f (h' i) + f x := by congr; convert concat_finite_series _ _ _ <;> grind

    rw [h3]
    congr 1

    have g_ne_x {i:ℤ} (hi : i ∈ Icc (1:ℤ) n) : g i ≠ x
    · have := g_bij.injective.eq_iff (a := ⟨i, by grind⟩) (b := ⟨n + 1, by grind⟩)
      simp only [Subtype.mk.injEq] at this
      change ¬ g i = g (n + 1)
      grind
    have h'_ne_x {i:ℤ} (hi : i ∈ Icc (1:ℤ) n) : h' i ≠ x
    · unfold h'
      split_ifs
      next hij =>
        have := h_bij.injective.eq_iff (a := ⟨i, by grind⟩) (b := ⟨j, by grind⟩)
        simp only [Subtype.mk.injEq] at this
        grind
      next hij =>
        have := h_bij.injective.eq_iff (a := ⟨i + 1, by grind⟩) (b := ⟨j, by grind⟩)
        simp only [Subtype.mk.injEq] at this
        grind

    refine ih (X.erase x) ?_ g h' ?_ ?_ ?_ ?_
    · rw [Finset.card_erase_of_mem (hg1 _ (by simp)), hcard]
      simp
    · intro i hi
      rw [mem_erase]
      exact ⟨g_ne_x hi, hg1 _ (by grind)⟩
    · intro i hi
      rw [mem_erase]
      refine ⟨h'_ne_x hi, ?_⟩
      unfold h'
      split_ifs <;> exact hh1 _ (by grind)

    -- TODO these bijectivity proofs are very ugly
    · rw [Function.bijective_iff_existsUnique] at g_bij ⊢
      intro ⟨y, hy⟩
      obtain ⟨hy1, hy2⟩ := mem_erase.mp hy
      specialize g_bij ⟨y, hy2⟩
      simp at g_bij ⊢
      obtain ⟨z, hz, hzuniq⟩ := g_bij
      refine ⟨⟨z, by grind⟩, ?_, ?_⟩
      · simpa
      · intro z' hz'
        specialize hzuniq ⟨z', by grind⟩ hz'
        simp [← hzuniq]
    · rw [Function.bijective_iff_existsUnique] at ⊢
      intro ⟨y, hy⟩
      obtain ⟨hy1, hy2⟩ := mem_erase.mp hy
      have := (Function.bijective_iff_existsUnique _).mp h_bij ⟨y, hy2⟩
      simp at this ⊢
      have ⟨z, hz, hzuniq⟩ := this
      simp [← hj] at hy1
      have : z ≠ j
      · grind
      by_cases hzj : z < j
      · refine ⟨⟨z, by grind⟩, ?_, ?_⟩
        · simpa [h', hzj]
        · intro z' hz'
          by_cases hzj' : z' < j
          · simp [h', hzj'] at hz'
            specialize hzuniq ⟨z', by grind⟩ hz'
            simp [← hzuniq]
          · simp [h', hzj'] at hz'
            rw [← hz] at hz'
            have : z'.val + 1 ∈ Icc (1:ℤ) (n + 1)
            · grind
            have := @h_bij.injective.eq_iff (a := ⟨_, this⟩) (b := z)
            grind
      · have hzj : ¬ z ≤ j
        · grind
        refine ⟨⟨z - 1, by grind⟩, ?_, ?_⟩
        · simpa [h', hzj]
        · intro z' hz'
          by_cases hzj' : z' < j
          · simp [h', hzj'] at hz'
            rw [← hz] at hz'
            have := @h_bij.injective.eq_iff (a := ⟨z', by grind⟩) (b := z)
            grind
          · simp [h', hzj'] at hz'
            rw [← hz] at hz'
            have : z'.val + 1 ∈ Icc (1:ℤ) (n + 1)
            · grind
            have := @h_bij.injective.eq_iff (a := ⟨z' + 1, by grind⟩) (b := z)
            grind


/-
This is the original `finite_series_of_rearrange`.
Starts with the same technical `π` step followed by an application of `finite_series_of_rearrange_Icc`.
-/
theorem finite_series_of_rearrange_orig {n:ℕ} {X':Type*} (X: Finset X') (hcard: X.card = n)
  (f: X' → ℝ) (g h: Icc (1:ℤ) n → X) (hg: Function.Bijective g) (hh: Function.Bijective h) :
    ∑ i ∈ Icc (1:ℤ) n, (if hi:i ∈ Icc (1:ℤ) n then f (g ⟨ i, hi ⟩) else 0)
    = ∑ i ∈ Icc (1:ℤ) n, (if hi: i ∈ Icc (1:ℤ) n then f (h ⟨ i, hi ⟩) else 0) := by
  cases n with
  | zero => simp
  | succ n =>
    -- A technical step: we extend g, h to the entire integers using a slightly artificial map π
    set π : ℤ → Icc (1:ℤ) (n+1) :=
      fun i ↦ if hi: i ∈ Icc (1:ℤ) (n+1) then ⟨ i, hi ⟩ else ⟨ 1, by simp ⟩
    have hπ (g : Icc (1:ℤ) (n+1) → X) :
        ∑ i ∈ Icc (1:ℤ) (n+1), (if hi:i ∈ Icc (1:ℤ) (n+1) then f (g ⟨ i, hi ⟩) else 0)
        = ∑ i ∈ Icc (1:ℤ) (n+1), f (g (π i)) := by
      apply sum_congr rfl _
      intro i hi; simp [hi, π, -mem_Icc]
    simp [-mem_Icc, hπ]

    apply finite_series_of_rearrange_Icc _ hcard
    · simp
    · simp
    · intro a b hab
      simp [π] at hab
      convert hg.injective hab <;> grind
    · intro a b hab
      simp [π] at hab
      convert hh.injective hab <;> grind

/-
Adapt the proof of `finite_series_of_rearrange_Icc_left` by choosing an `x` from `X`.
Then split the sets into `X = X.erase x ∪ {x}` and `Y = Y.erase (g x) ∪ {g x}`, use `sum_union` and congruence.
Conclude with `∑ x ∈ X.erase x, f (g x) = ∑ x ∈ Y.erase (g x), f x` using the induction hypothesis.
-/
theorem finite_series_of_rearrange_finset_left {n : ℕ} {X' : Type*} {X Y : Finset X'} (cardX : X.card = n) (cardY : Y.card = n) {f : X' → ℝ} {g : X' → X'}
    (hg : ∀ i ∈ X, g i ∈ Y) (ginj : Function.Injective (X.restrict g)) :
    ∑ i ∈ X, f (g i) = ∑ i ∈ Y, f i := by
  classical
  induction n generalizing X Y with
  | zero =>
    rw [card_eq_zero] at cardX cardY
    simp [cardX, cardY]
  | succ n ih =>
    obtain ⟨x, hx⟩ : X.Nonempty
    · rw [← Finset.card_ne_zero]
      grind

    rw [show X = X.erase x ∪ {x} by grind, show Y = Y.erase (g x) ∪ {g x} by grind]

    rw [sum_union' (by simp), sum_union' (by simp), sum_singleton, sum_singleton]

    congr 1
    apply ih
    · grind
    · grind
    · intro i hi
      have := @ginj.eq_iff (a := ⟨i, by grind⟩) (b := ⟨x, hx⟩)
      simp at this
      grind
    · intro a b hab
      specialize @ginj ⟨a, by grind⟩ ⟨b, by grind⟩
      simp at hab ginj
      grind

/-
Adapt this from `finite_series_of_rearrange_Icc`.
-/
theorem finite_series_of_rearrange_finset {n : ℕ} {X' : Type*} {X Y : Finset X'} (cardX : X.card = n) (cardY : Y.card = n) {f : X' → ℝ} {g h : X' → X'}
    (hg : ∀ i ∈ X, g i ∈ Y) (ginj : Function.Injective (X.restrict g))
    (hh : ∀ i ∈ X, h i ∈ Y) (hinj : Function.Injective (X.restrict h)) :
    ∑ i ∈ X, f (g i) = ∑ i ∈ X, f (h i) := by
  calc ∑ i ∈ X, f (g i)
    _ = ∑ i ∈ Y, f i := by apply finite_series_of_rearrange_finset_left cardX cardY hg ginj
    _ = ∑ i ∈ X, f (h i) := symm (finite_series_of_rearrange_finset_left cardX cardY hh hinj)


section attach


-- Trying to work with attach directly leads to a complete mess
-- theorem finite_series_of_rearrange_attach_left {X':Type*} {X Y : Finset X'} {f : X' → ℝ} (g : X → Y) (hg: Function.Bijective g) :
--     ∑ i ∈ Y, f i = ∑ i ∈ X.attach, f (g i) := by
--   classical
--   induction hcard : #X generalizing X Y with
--   | zero =>
--     have cardY : #Y = 0
--     · rw [← hcard, card_eq_of_equiv (Equiv.ofBijective g hg)]
--     rw [card_eq_zero] at *
--     rw! (castMode := .all) [cardY, hcard]
--     simp
--   | succ n ih =>
--     have cardY : #Y = n + 1
--     · rw [← hcard, card_eq_of_equiv (Equiv.ofBijective g hg)]

--     -- rw [sum_attach_eq_sum_with]

--     obtain ⟨x, hx⟩ : X.Nonempty
--     · rw [← Finset.card_ne_zero]
--       grind

--     have hY : Y = (Y.erase (g ⟨x, hx⟩) ∪ {(g ⟨x, hx⟩).val}) := by grind
--     have hX : X = (X.erase x ∪ {x}) := by grind
--     -- rw! (castMode := .all) [hY, hX]
--     have : ∑ i ∈ X.attach, f (g i) = ∑ i ∈ X with hi : i ∈ (X.erase x ∪ {x}), f (g ⟨i, by grind⟩)
--     · rw [sum_attach_eq_sum_with]
--       apply sum_congr rfl
--       grind

--     have : ∑ i ∈ Y, f i = ∑ i ∈ (Y.erase (g ⟨x, hx⟩) ∪ {(g ⟨x, hx⟩).val}), f i
--     · grind

--     rw [this]

--     have : ∑ i ∈ X.attach, f (g i) = ∑ i ∈ (X.erase x ∪ {x}) with hi : i ∈ (X.erase x ∪ {x}), f (g ⟨i, by grind⟩)
--     · sorry

--     rw [this]

--     rw [sum_union' (by simp), sum_union' (by simp), sum_singleton, sum_singleton]

--     congr 1
--     ·
--       rw [sum_dite_of_true (by grind)]
--       -- conv_rhs => rw [← sum_attach_eq_sum_with (s := X.erase x)]
--       specialize ih (X := (X.erase x ∪ {x})) (Y := (Y.erase (g ⟨x, hx⟩) ∪ {(g ⟨x, hx⟩).val}))
--       sorry
--     sorry

end attach
