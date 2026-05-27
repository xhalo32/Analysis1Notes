import Mathlib.Tactic

/-!
# 7.1. Finite series

Source: https://teorth.github.io/analysis/Analysis/Section_7_1/.

To begin with, I want to note that most of the theorems in the material are given terrible names.
I renamed and made other alterations to the exercises.

The idea of definition 7.1.6 probably was to transport the theorems `finite_series_eq`, however it's very tedious to use as one has to pass in the bijection whose existence comes from `exist_bijection`.
Therefore I've made the decision to focus on the API provided by mathlib rather than building our own.

TODO split the sections into their own files in the Section-7-1 directory
-/

open Finset

section sum_icc

/-
## Sums over intervals

In this section, we are going to work through some basic exercises involving finite sums over intervals `[m, n]`.

The idea is to use `sum_of_empty` and `sum_of_nonempty` as the primary tools when solving the exercises.
Feel free to also use API provided by mathlib.
Tools like `sum_singleton` and `sum_union` are proved as part of later exercises.
-/

/-
The first two theorems are already done in https://teorth.github.io/analysis/Analysis/Section_7_1/.
Should you want to attempt them yourself, here are some useful lemmas:

- `rw [Icc_eq_empty_iff.mpr]`, `sum_empty`, `sum_eq_zero`
- `rw [← insert_Icc_right_eq_Icc_add_one]`
- `sum_insert`
-/
theorem sum_of_empty {n m:ℤ} (h: n < m) (a: ℤ → ℝ) : ∑ i ∈ Icc m n, a i = 0 := by
  rw [Icc_eq_empty_iff.mpr (by grind)]
  exact sum_empty

theorem sum_of_nonempty {n m:ℤ} (h: n ≥ m-1) (a: ℤ → ℝ) :
    ∑ i ∈ Icc m (n+1), a i = ∑ i ∈ Icc m n, a i + a (n+1) := by
  rw [← insert_Icc_right_eq_Icc_add_one (by grind)]
  rw [sum_insert (by simp)]
  ac_rfl

/-
Practice using `sum_of_empty` and `sum_of_nonempty`.
-/
example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-2), a i = 0 := by
  rw [sum_of_empty]
  simp

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-1), a i = 0 := by
  rw [sum_of_empty]
  simp

/-
See `Icc_self`
-/
example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m m, a i = a m := by
  rw [Icc_self, sum_singleton]

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+1), a i = a m + a (m+1) := by
  rw [sum_of_nonempty]
  · rw [Icc_self, sum_singleton]
  · simp

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+2), a i = a m + a (m+1) + a (m+2) := by
  have : Icc m (m + 2) = {m, m+1, m+2}
  · grind
  rw [this]
  simp
  ring

/-
There are at least two different approaches to this:
1. Induction in `p`. Start with `induction p, hpn using Int.le_induction`.
2. Combine sums to `Icc m n ∪ Icc (n + 1) p` and show `Icc m n ∪ Icc (n + 1) p = Icc m p`. Start with `rw [← sum_union]`.
-/
theorem concat_sum {m n p:ℤ} (hmn: m ≤ n+1) (hpn : n ≤ p) (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc (n+1) p, a i = ∑ i ∈ Icc m p, a i := by
  have union_eq : Icc m n ∪ Icc (n + 1) p = Icc m p
  · ext l
    simp only [mem_union, mem_Icc]
    omega
  have inter_eq : Icc m n ∩ Icc (n + 1) p = ∅
  · ext l
    simp only [mem_inter, mem_Icc, notMem_empty, iff_false]
    omega
  rw [← sum_union (disjoint_iff_inter_eq_empty.mpr inter_eq), union_eq]
  -- Approach 1:
  -- induction p, hpn using Int.le_induction with
  -- | base =>
  --   nth_rw 2 [sum_of_empty] <;> simp
  -- | succ p hmn ih =>
  --   rw [sum_of_nonempty, ← add_assoc, ih, sum_of_nonempty] <;> grind

/-
Here, I think induction is straigthest forward.
Start with `by_cases hmn : m ≤ n` followed by `induction n, hmn using Int.le_induction`.
-/
theorem shift_sum {m n k:ℤ} (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i = ∑ i ∈ Icc (m+k) (n+k), a (i-k) := by
  by_cases hmn : m ≤ n
  · induction n, hmn using Int.le_induction with
    | base =>
      simp
    | succ n hmn ih =>
      rw [show ∀ k, n + 1 + k = n + k + 1 by simp +arith]
      rw [sum_of_nonempty, ih, sum_of_nonempty] <;> grind
  · rw [sum_of_empty, sum_of_empty] <;> grind

/-
Again, try induction: `by_cases hmn : m ≤ n` followed by `induction n, hmn using Int.le_induction`.
-/
theorem sum_add_distrib_Icc {m n:ℤ} (a b: ℤ → ℝ) :
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
          rw [sum_of_nonempty (by grind), sum_of_nonempty (by grind)]
  · rw [sum_of_empty, sum_of_empty, sum_of_empty] <;> grind

/-
Straight-forward with the same induction approach.
-/
theorem sum_mul_Icc {m n:ℤ} (a: ℤ → ℝ) (c:ℝ) :
  ∑ i ∈ Icc m n, c * a i = c * ∑ i ∈ Icc m n, a i := by
  by_cases hmn : m ≤ n
  · induction n, hmn using Int.le_induction with
    | base =>
      simp
    | succ n hmn ih =>
      rw [sum_of_nonempty (by grind), ih, ← mul_add, ← sum_of_nonempty (by grind)]
  · rw [sum_of_empty, sum_of_empty, mul_zero] <;> grind

/-
Straight-forward with the same induction approach.
Use of `grw` tactic is recommended

Hints:
1. Induction step: `sum_of_nonempty`, `abs_add_le`, and then `ih`.
-/
theorem abs_sum_le_sum_abs_Icc {m n:ℤ} (a: ℤ → ℝ) :
  |∑ i ∈ Icc m n, a i| ≤ ∑ i ∈ Icc m n, |a i| := by
  by_cases hmn : m ≤ n
  · induction n, hmn using Int.le_induction with
    | base =>
      simp
    | succ n hmn ih =>
      calc |∑ i ∈ Icc m (n + 1), a i|
        _ = |(∑ i ∈ Icc m n, a i) + a (n + 1)| := by rw [sum_of_nonempty (by grind)]
        _ ≤ |∑ i ∈ Icc m n, a i| + |a (n + 1)| := abs_add_le _ _
        _ ≤ ∑ i ∈ Icc m n, |a i| + |a (n + 1)| := by grw [ih]
        _ ≤ ∑ i ∈ Icc m (n + 1), |a i| := by rw [sum_of_nonempty (by grind)]
      -- or just grw [sum_of_nonempty (by grind), abs_add_le, ih, sum_of_nonempty (by grind)]
  · rw [sum_of_empty, sum_of_empty, abs_zero] <;> grind

theorem sum_le_sum_Icc {m n:ℤ}  {a b: ℤ → ℝ} (h: ∀ i, m ≤ i → i ≤ n → a i ≤ b i) :
  ∑ i ∈ Icc m n, a i ≤ ∑ i ∈ Icc m n, b i := by
  by_cases hmn : m ≤ n
  · induction n, hmn using Int.le_induction with
    | base =>
      simp [h _ le_rfl le_rfl]
    | succ n hmn ih =>
      grw [sum_of_nonempty, ih, h, ← sum_of_nonempty] <;> grind
  · rw [sum_of_empty, sum_of_empty] <;> grind

/-
Next, we prove a "one-sided" reformulation of `finite_series_of_rearrange` that avoids the technicalities with `π`.
The main difference is that the domain of `g` is ℤ rather than `Icc (1:ℤ) n` and codomain is `X'` rather than `X`.
This avoids having to deal with subtypes inside the sums.
The assumption `hg` which gives the restriction on the range of `g` is unbundled.

The proof sketch:
1. Proceed with induction in `n` generalizing `X`, zero step is trivial.
2. Let `x = g (n + 1)` and write `X = X.erase x ∪ {x}`.
3. Split the `f x` term from the sums.
4. By congruence, it suffices to show `∑ i ∈ Icc 1 ↑n, f (g i) = ∑ x ∈ X.erase x, f x` which is immediate from the induction hypothesis with as `#(X.erase x) = n`.

Notes:
- Finset ∪-notation requires `classical`.
- The proof relies on `sum_union`, which is proved in the next section.
- To utilize injectivity, start with `have := @ginj.eq_iff (a := ⟨i, by grind⟩) (b := ⟨n + 1, by simp⟩)` followed by `simp at this`.
-/
theorem sum_rearrange_Icc_left {n : ℕ} {X' : Type*} {X : Finset X'} (hcard : X.card = n) {f : X' → ℝ} {g : ℤ → X'} (hg : ∀ i ∈ Icc (1:ℤ) n, g i ∈ X) (ginj : Function.Injective ((Icc (1:ℤ) n).restrict g)) :
    ∑ i ∈ Icc (1:ℤ) n, f (g i) = ∑ i ∈ X, f i := by
  classical
  induction n generalizing X with
  | zero =>
    rw [card_eq_zero] at hcard
    simp [hcard]
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    let x := g (n + 1)

    rw [show X = X.erase x ∪ {x} by grind, sum_union (by simp), sum_singleton, sum_of_nonempty (by simp)]

    congr 1
    apply ih
    · grind
    · intro i hi
      have := @ginj.eq_iff (a := ⟨i, by grind⟩) (b := ⟨n + 1, by simp⟩)
      simp at this
      grind
    · intro a b hab
      specialize @ginj ⟨a, by grind⟩ ⟨b, by grind⟩
      simp at hab ginj
      grind

/-
The two-sided version with two bijections `g` and `h` is a corollary of applying `sum_rearrange_Icc_left` twice.
-/
theorem sum_rearrange_Icc {n:ℕ} {X':Type*} (X: Finset X') (hcard: X.card = n) (f: X' → ℝ) (g h: ℤ → X')
  (hg : ∀ i ∈ Icc (1:ℤ) n, g i ∈ X)
  (hh : ∀ i ∈ Icc (1:ℤ) n, h i ∈ X)
  (ginj: Function.Injective ((Icc (1:ℤ) n).restrict g))
  (hinj: Function.Injective ((Icc (1:ℤ) n).restrict h)) :
    ∑ i ∈ Icc (1:ℤ) n, f (g i) = ∑ i ∈ Icc (1:ℤ) n, f (h i) := by
  calc ∑ i ∈ Icc (1:ℤ) n, f (g i)
    _ = ∑ i ∈ X, f i := sum_rearrange_Icc_left hcard hg ginj
    _ = ∑ i ∈ Icc (1:ℤ) n, f (h i) := symm (sum_rearrange_Icc_left hcard hh hinj)

end sum_icc

section sum_finset

/-
In this section, instead of working with intervals, we move on to arbitrary finite sets.
All the theorems that start with `_` are already in mathlib without the prefix (to suitable generality).

Summing over a finset is defined as mapping over the underlying multiset and folding over the mapped multiset while accumulating the sum.

Conveniently this means that `finite_series_of_empty` is true by definitional equality, because mapping over ∅ returns ∅ and folding over ∅ returns the base value which is 0.

## API overview

API for working with sums:
- `sum_empty`
- `sum_insert` (usually needs `DecidableEq` or `classical`)
- Induction using `Finset.induction`

API for Finsets:
- `insert_union`
- I have also created `singleton_def`.

API for `Disjoint` Finsets:
- `disjoint_insert_left`/`right`
- `disjoint_union_left`/`right`
-/

example {X' : Type*} {f : X' → ℝ} {s : Finset X'} : ∑ i ∈ s, f i = Multiset.fold (fun x y : ℝ => x + y) 0 (Multiset.map f s.val) := rfl

lemma Finset.singleton_def {X' : Type*} [DecidableEq X'] {x : X'} : ({x} : Finset X') = insert x ∅ := rfl

theorem _sum_empty {X':Type*} (f: X' → ℝ) : ∑ i ∈ ∅, f i = 0 := by
  rfl

/-
This is a straight-forward application of `sum_insert` after rewriting with `singleton_def`.
-/
theorem _sum_singleton {X':Type*} [DecidableEq X'] (f: X' → ℝ) (x₀:X') : ∑ i ∈ {x₀}, f i = f x₀ := by
  rw [singleton_def, sum_insert, sum_empty, add_zero]
  simp

/-
Notes:
- `∑ x, f x`, is a shorthand for `∑ x ∈ Finset.univ, f x`.
- `sum_coe_sort`
-/

/-
Now we prove `sum_union` which we relied upon in the rearrangement theorem.
This is a standard Finset induction proof.

Start with `induction X using Finset.induction`.
See `disjoint_insert_left`.
-/
theorem _sum_union {α : Type*} {X Y : Finset α} [DecidableEq α] {f : α → ℝ} (h : Disjoint X Y)
    : ∑ x ∈ X ∪ Y, f x = ∑ x ∈ X, f x + ∑ y ∈ Y, f y := by
  induction X using Finset.induction with
  | empty =>
    rw [empty_union, sum_empty, zero_add]
  | insert a s ha ih =>
    rw [disjoint_insert_left] at h
    rw [insert_union, sum_insert, sum_insert, ih h.2, add_assoc] <;> grind

/-
This is another standard Finset induction proof.

Hints:
1. Start with `simp_rw [Pi.add_apply]` followed by `induction X using Finset.induction`
-/
theorem _sum_add_distrib {X':Type*} [DecidableEq X'] (f g: X' → ℝ) (X: Finset X') :
    ∑ x ∈ X, (f + g) x = ∑ x ∈ X, f x + ∑ x ∈ X, g x := by
  simp_rw [Pi.add_apply]
  induction X using Finset.induction with
  | empty =>
    rw [sum_empty, sum_empty, sum_empty, add_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha, sum_insert ha, ih]
    ring

/-
Keyword: Finset induction.
-/
theorem _sum_mul {X':Type*} [DecidableEq X'] (f: X' → ℝ) (X: Finset X') (c:ℝ) :
    ∑ x ∈ X, c * f x = c * ∑ x ∈ X, f x := by
  induction X using Finset.induction with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha, ih]
    ring

/-
You guessed it, Finset induction!
-/
theorem _sum_le_sum {X':Type*} [DecidableEq X'] (f g: X' → ℝ) (X: Finset X') (h: ∀ x ∈ X, f x ≤ g x) :
    ∑ x ∈ X, f x ≤ ∑ x ∈ X, g x := by
  induction X using Finset.induction with
  | empty =>
    simp
  | insert a s ha ih =>
    grw [sum_insert ha, h, ih, sum_insert ha]
    · grind
    · simp

/-
`abs_finite_series_le` + Finset induction.
-/
theorem _abs_sum_le_sum_abs {X':Type*} [DecidableEq X'] (f: X' → ℝ) (X: Finset X') :
    |∑ x ∈ X, f x| ≤ ∑ x ∈ X, |f x| := by
  induction X using Finset.induction with
  | empty =>
    simp
  | insert a s ha ih =>
    grw [sum_insert ha, abs_add_le, ih, sum_insert ha]

/-
Start with Finset induction.
Here are some lemmas for working with a cartesian product (`×ˢ`):
- `union_product`
- `disjoint_product`

Hints:
1. Rewrite `← singleton_union`.
2. `union_product`
3. `∑ x ∈ {a} ×ˢ Y, f x = ∑ y ∈ Y, f (a, y)` is true by `simp`
-/
theorem _sum_product {XX YY:Type*} [DecidableEq XX] [DecidableEq YY] (X: Finset XX) (Y: Finset YY)
  (f: XX × YY → ℝ) :
    ∑ z ∈ X ×ˢ Y, f z = ∑ x ∈ X, ∑ y ∈ Y, f (x, y) := by
  induction X using Finset.induction with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [sum_insert ha, ← ih]
    rw [← singleton_union, union_product, sum_union]
    · congr
      simp
    rw [disjoint_product]
    simp [ha]

/-
This is "Fubini's theorem for sums". Cartesian product flavor.
The proof is simple using another formulation of rearrangement called `sum_nbij`.
Start with `apply sum_nbij (i := Prod.swap)`.
-/
theorem sum_product_comm {XX YY:Type*} [DecidableEq XX] [DecidableEq YY] (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ z ∈ X ×ˢ Y, f z = ∑ z ∈ Y ×ˢ X, f (z.2, z.1) := by
  apply sum_nbij (i := Prod.swap)
  · grind
  · exact Prod.swap_bijective.injective.injOn
  · intro x hx
    simp
    grind
  · grind

/-
This is Fubini for nested sums.
-/
theorem _sum_comm {XX YY:Type*} [DecidableEq XX] [DecidableEq YY] (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ y ∈ Y, ∑ x ∈ X, f (x, y) := by
  rw [← sum_product, sum_product_comm, sum_product]

/-
A useful variant of sum rearrangement is `sum_nbij` in mathlib, which we will prove next.
It is a special case of `sum_bij` and has a cleaner API in my opinion (e.g. it uses `SurjOn`).

The proof mirrors that of `finite_series_of_rearrange_Icc_left` using induction in the Finset `s` instead of `n`.
The base case takes a bit more work, but the inductive step gives you a choice of `a` (analogue of `x`).

Hints:
1. Start with `induction s using Finset.induction generalizing t`
2. In the base step `empty` show `t = ∅` first
3. In the `insert` induction step, show `t = t.erase (i a) ∪ {i a}`
4. Extract `f a` from the left sum and `g (i a)` from the right, prove that they are equal.
5. Use `congr` and apply the induction hypothesis. The first goal needs injectivity, which you can get with `have := @i_inj.eq_iff`. You also need to use `a ∉ s`.
-/
theorem _sum_nbij [AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (i : ι → κ) (hi : ∀ a ∈ s, i a ∈ t) (i_inj : (s : Set ι).InjOn i)
    (i_surj : (s : Set ι).SurjOn i t) (h : ∀ a ∈ s, f a = g (i a)) :
    ∑ x ∈ s, f x = ∑ x ∈ t, g x := by
  classical
  induction s using Finset.induction generalizing t with
  | empty =>
    have : t = ∅
    · rw [← subset_empty]
      intro x hx
      specialize i_surj hx
      grind
    simp [this]
  | insert a s ha ih =>
    have : t = t.erase (i a) ∪ {i a}
    · grind
    rw [this, sum_insert ha, add_comm, sum_union (by simp), sum_singleton]
    rw [show f a = g (i a) by grind]
    congr
    apply ih
    · intro x hx
      specialize h x (by grind)
      have := @i_inj.eq_iff
      grind
    · rw [coe_insert, Set.injOn_insert ha] at i_inj
      exact i_inj.1
    · rw [coe_insert] at i_surj
      intro k hk
      simp only [coe_erase, Set.mem_diff] at hk
      specialize i_surj hk.1
      grind
    · grind

-- `hi` is equivalent with `Set.MapsTo i s t` which means that `hi, i_inj, i_surj` are exactly `Set.BijOn i s t`
example : (∀ a ∈ s, i a ∈ t) ↔ Set.MapsTo i s t := Iff.rfl

/-
This is an immediate consequence of `sum_nbij`. Start with `symm` followed by `apply sum_nbij g`.
-/
theorem map_finite_series {X Y:Type*} [Fintype X] [Fintype Y] (f: X → ℝ) {g:Y → X}
  (hg: Function.Bijective g) :
    ∑ x, f x = ∑ y, f (g y) := by
  symm
  apply sum_nbij g
  · simp
  · exact hg.injective.injOn
  · simp [hg.surjective]
  · simp

end sum_finset

section challenges

open scoped Nat

variable {ι κ G M : Type*}
variable [CommMonoid M]

@[to_additive]
lemma prod_attach_eq_iff (s : Finset ι) (t : Finset κ) (f : ι → M) (g : κ → M) : (∏ x ∈ s, f x = ∏ y ∈ t, g y) ↔ (∏ x ∈ s.attach, f x = ∏ y ∈ t.attach, g y) := by
  rw [prod_attach, prod_attach]

-- This is missing from mathlib
@[grind .]
lemma zpow_succ {a : ℝ} (j : ℤ) (hj : 0 ≤ j) : a^(j + 1) = a * a^j := by
  lift j to ℕ using by grind
  norm_cast
  rw [pow_succ']

example {x y : ℝ} {n : ℕ} : ∑ j ∈ Icc (0:ℤ) n, n.choose j.toNat * x * x^j * y^(n - j) = ∑ j ∈ Icc (0:ℤ) n, n.choose j.toNat * x^(j + 1) * y^(n - j) := by
  rw [sum_attach_eq_iff, sum_congr rfl]
  intro j hj
  rw [zpow_succ]
  · grind
  · grind

/-
I recommend following this proof:
https://math.stackexchange.com/questions/1695270/binomial-theorem-proof-by-induction
Notice however that the roles of x and y are flipped.

`grind` can mostly solve the algebraic manipulations, however you will likely need the following tools:
- `mul_sum`
- `concat_sum`
- `shift_sum`
- `sum_add_distrib`
- `Nat.choose_succ_left` (Pascal's identity)
- `sum_attach_eq_iff` when going from `∑ j ∈ Icc (0:ℤ) n, n.choose j.toNat * x * x^j * y^(n - j)` to `∑ j ∈ Icc (0:ℤ) n, n.choose j.toNat * x^(j + 1) * y^(n - j)`. See the example above.
- `Int.toNat_sub''`, `Int.toNat_one` and `norm_cast` are useful for working around the `toNat`
-/
theorem binomial_theorem (x y:ℝ) (n:ℕ) :
    (x + y)^n = ∑ j ∈ Icc (0:ℤ) n, Nat.choose n j.toNat * x^j * y^(n - j) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    calc (x + y)^(n + 1)
      _ = (x + y) * (x + y)^n := by grind
      _ = x * ∑ j ∈ Icc (0:ℤ) n, n.choose j.toNat * x^j * y^(n - j)
        + y * ∑ j ∈ Icc (0:ℤ) n, n.choose j.toNat * x^j * y^(n - j) := by grind
      _ = ∑ j ∈ Icc (0:ℤ) n, n.choose j.toNat * x * x^j * y^(n - j)
        + ∑ j ∈ Icc (0:ℤ) n, n.choose j.toNat * x^j * y * y^(n - j) := by rw [mul_sum, mul_sum]; grind
      _ = ∑ j ∈ Icc (0:ℤ) n, n.choose j.toNat * x^(j + 1) * y^(n - j)
        + ∑ j ∈ Icc (0:ℤ) n, n.choose j.toNat * x^j * y^(n + 1 - j) := by
          congr 1
          · rw [sum_attach_eq_iff]
            grind
          · rw [sum_attach_eq_iff]
            grind
      _ = (n.choose n * x^(n + 1) + ∑ j ∈ Icc (0:ℤ) (n-1), n.choose j.toNat * x^(j + 1) * y^(n - j))
        + (n.choose 0 * y^(n + 1) + ∑ j ∈ Icc (1:ℤ) n,     n.choose j.toNat * x^j * y^(n + 1 - j)) := by
          congr 1
          · rw [← concat_sum (n := n-1) (by grind) (by grind)]
            simp
            ac_rfl
          · rw [← concat_sum (n := 0) (by grind) (by grind)]
            simp
            norm_cast
      _ = x^(n + 1) + y^(n + 1)
        + ∑ j ∈ Icc (0:ℤ) (n-1), n.choose j.toNat * x^(j + 1) * y^(n - j)
        + ∑ j ∈ Icc (1:ℤ) n, n.choose j.toNat * x^j * y^(n + 1 - j) := by simp; grind
      _ = (n+1).choose (n+1) * x^(n + 1) + (n+1).choose 0 * y^(n + 1)
        + ∑ j ∈ Icc (0:ℤ) (n-1), n.choose j.toNat * x^(j + 1) * y^(n - j)
        + ∑ j ∈ Icc (1:ℤ) n, n.choose j.toNat * x^j * y^(n + 1 - j) := by simp
      _ = (n+1).choose (n+1) * x^(n + 1) + (n+1).choose 0 * y^(n + 1)
        + ∑ j ∈ Icc (1:ℤ) n, n.choose (j-1).toNat * x^(j - 1 + 1) * y^(n - (j - 1))
        + ∑ j ∈ Icc (1:ℤ) n, n.choose j.toNat * x^j * y^(n + 1 - j) := by congr 1; congr 1; rw [shift_sum (k := 1)]; grind
      _ = (n+1).choose (n+1) * x^(n + 1) + (n+1).choose 0 * y^(n + 1)
        + ∑ j ∈ Icc (1:ℤ) n, (n.choose (j-1).toNat * x^(j - 1 + 1) * y^(n - (j - 1))
                             + n.choose j.toNat * x^j * y^(n + 1 - j)) := by rw [sum_add_distrib]; grind
      _ = (n+1).choose (n+1) * x^(n + 1) + (n+1).choose 0 * y^(n + 1)
        + ∑ j ∈ Icc (1:ℤ) n, (n.choose (j-1).toNat * x^j * y^(n + 1 - j)
                             + n.choose j.toNat * x^j * y^(n + 1 - j)) := by grind
      _ = (n+1).choose (n+1) * x^(n + 1) + (n+1).choose 0 * y^(n + 1)
        + ∑ j ∈ Icc (1:ℤ) n, ((n.choose (j-1).toNat + n.choose j.toNat) * x^j * y^(n + 1 - j)) := by grind
      _ = (n+1).choose (n+1) * x^(n + 1) + (n+1).choose 0 * y^(n + 1)
        + ∑ j ∈ Icc (1:ℤ) n, (((n + 1).choose j.toNat) * x^j * y^(n + 1 - j)) := by
          congr 1
          rw [sum_attach_eq_iff, sum_congr rfl]
          intro j hj
          rw [Nat.choose_succ_left _ _ (by grind), Int.toNat_sub'' (by grind) (by simp), Int.toNat_one]
          norm_cast
      _ = ∑ j ∈ Icc (0:ℤ) (n+1), (((n + 1).choose j.toNat) * x^j * y^(n + 1 - j)) := by
          conv_rhs => rw [sum_of_nonempty (by simp), ← concat_sum (n := 0) (by grind) (by grind)]
          simp [zpow_succ]
          grind

/-
This is surprisingly straight-forward with Finset induction.
To get going, we notice that `∑ x, ...` is notation for `∑ x ∈ univ, ...` which means that we should do induction in `univ`.
To do this, you can write `induction (univ : Finset X) using Finset.induction`.

Side note: to extract the `univ` as a Finset `X'`, you can use `set X' := (univ : Finset X)`, although this is not necessary.

Hints:
1. Remember that `simp` and `simp_rw` can't dispatch further goals, so to use `sum_insert` you need to provide it with the hypothesis `hx : x ∉ s` (in the case where the branch introduces the variables `insert x s hx ih`).
-/
open Filter in
theorem tendsto_sum_sum {X:Type*} [DecidableEq X] [Fintype X] (a: X → ℕ → ℝ) (L : X → ℝ)
  (h: ∀ x, atTop.Tendsto (a x) (nhds (L x))) :
    atTop.Tendsto (fun n ↦ ∑ x, a x n) (nhds (∑ x, L x)) := by
  -- set X' := (univ : Finset X)
  induction (univ : Finset X) using Finset.induction with
  | empty =>
    simp
  | insert x s hx ih =>
    simp [sum_insert hx]
    exact Tendsto.add (h x) ih

#check Finset.Icc_diff_both

/-

- `Fin.sum_univ_succ`
- `Fin.sum_univ_castSucc`
- `sum_attach`
-/
theorem sum_partition {n : ℕ} {S : Type*} [Fintype S]
    (E : Fin n → Finset S)
    (disj : ∀ i j : Fin n, i ≠ j → Disjoint (E i) (E j))
    (cover : ∀ s : S, ∃ i, s ∈ E i) -- univ = ⋃ i, E i
    (f : S → ℝ) :
    ∑ s : S, f s = ∑ i : Fin n, ∑ s ∈ E i, f s := by
  classical
  induction n generalizing f S with
  | zero =>
    by_cases hs : Nonempty S
    · obtain ⟨s⟩ := hs
      specialize cover s
      simp at cover
    · rw [not_nonempty_iff] at hs
      simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    -- This proof is really ugly
    let S' := (univ : Finset S) \ E 0
    have hE' (i : Fin n) : E i.succ ⊆ S'
    · unfold S'
      intro x hx
      simp
      by_contra hx0
      specialize disj 0 i.succ (by grind)
      rw [disjoint_iff_inter_eq_empty] at disj
      have : x ∈ E 0 ∩ E i.succ
      · grind
      grind

    let E' (i : Fin n) : Finset (E i.succ) := (E i.succ).attach
    let E'' (i : Fin n) : Finset S' := (E' i).map ⟨fun t => ⟨t.val, hE' i t.prop⟩, by
      intro a b hab
      simp at hab
      exact hab
    ⟩

    specialize ih E'' ?_ ?_ (fun x => f x)
    · intro i j hij
      specialize disj i.succ j.succ (by grind)
      rw [disjoint_iff_ne] at *
      intro s hs t ht
      unfold E'' at hs ht
      simp at hs ht
      grind
    · intro s
      obtain ⟨i, hi⟩ := cover s
      use i.pred (by grind)
      unfold E''
      simp
      grind
    · unfold S' E'' E' at ih
      simp at ih
      conv_rhs =>
        enter [2, 2, i]
        rw [← sum_attach]
      rw [← ih]
      rw [sum_attach]
      simp

theorem sum_finite_col_row_counts {n m : ℕ} (a : Fin n → Fin m) :
    ∑ i, (a i : ℕ) = ∑ j : Fin m, #{i : Fin n | j < a i}.toFinset := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have (j : Fin m) : #{i | j < a i}.toFinset = ∑ i, if j < a i then 1 else 0
    · simp
    simp_rw [this, Fin.sum_univ_castSucc]
    have (j : Fin m) : #{i : Fin n | j < a i.castSucc}.toFinset = ∑ i : Fin n, if j < a i.castSucc then 1 else 0
    · simp
    simp_rw [← this]
    rw [sum_add_distrib]
    rw [← ih]
    congr
    simp [filter_gt_eq_Iio]

end challenges
