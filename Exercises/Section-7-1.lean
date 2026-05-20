import Mathlib.Tactic

/-!
# 7.1. Finite series

Source: https://teorth.github.io/analysis/Analysis/Section_7_1/.

To begin with, I want to note that most of the theorems in the material are given terrible names.
I renamed and made other alterations to the exercises.

The idea of definition 7.1.6 probably was to transport the theorems `finite_series_eq`, however it's very tedious to use as one has to pass in the bijection whose existence comes from `exist_bijection`.
Therefore I've made the decision to focus on the API provided by mathlib rather than building our own.
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
  sorry

theorem sum_of_nonempty {n m:ℤ} (h: n ≥ m-1) (a: ℤ → ℝ) :
    ∑ i ∈ Icc m (n+1), a i = ∑ i ∈ Icc m n, a i + a (n+1) := by
  sorry

/-
Practice using `sum_of_empty` and `sum_of_nonempty`.
-/
example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-2), a i = 0 := by
  sorry

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-1), a i = 0 := by
  sorry

/-
See `Icc_self`
-/
example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m m, a i = a m := by
  sorry

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+1), a i = a m + a (m+1) := by
  sorry

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+2), a i = a m + a (m+1) + a (m+2) := by
  sorry

/-
There are at least two different approaches to this:
1. Induction in `p`. Start with `induction p, hpn using Int.le_induction`.
2. Combine sums to `Icc m n ∪ Icc (n + 1) p` and show `Icc m n ∪ Icc (n + 1) p = Icc m p`. Start with `rw [← sum_union]`.
-/
theorem concat_sum {m n p:ℤ} (hmn: m ≤ n+1) (hpn : n ≤ p) (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc (n+1) p, a i = ∑ i ∈ Icc m p, a i := by
  sorry

/-
Here, I think induction is straigthest forward.
Start with `by_cases hmn : m ≤ n` followed by `induction n, hmn using Int.le_induction`.
-/
theorem shift_sum {m n k:ℤ} (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i = ∑ i ∈ Icc (m+k) (n+k), a (i-k) := by
  sorry

/-
Again, try induction: `by_cases hmn : m ≤ n` followed by `induction n, hmn using Int.le_induction`.
-/
theorem sum_add_distrib_Icc {m n:ℤ} (a b: ℤ → ℝ) :
  ∑ i ∈ Icc m n, (a i + b i) = ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc m n, b i := by
  sorry

/-
Straight-forward with the same induction approach.
-/
theorem sum_mul_Icc {m n:ℤ} (a: ℤ → ℝ) (c:ℝ) :
  ∑ i ∈ Icc m n, c * a i = c * ∑ i ∈ Icc m n, a i := by
  sorry

/-
Straight-forward with the same induction approach.
Use of `grw` tactic is recommended

Hints:
1. Induction step: `sum_of_nonempty`, `abs_add_le`, and then `ih`.
-/
theorem abs_sum_le_sum_abs_Icc {m n:ℤ} (a: ℤ → ℝ) :
  |∑ i ∈ Icc m n, a i| ≤ ∑ i ∈ Icc m n, |a i| := by
  sorry

theorem sum_le_sum_Icc {m n:ℤ}  {a b: ℤ → ℝ} (h: ∀ i, m ≤ i → i ≤ n → a i ≤ b i) :
  ∑ i ∈ Icc m n, a i ≤ ∑ i ∈ Icc m n, b i := by
  sorry

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
  sorry

/-
The two-sided version with two bijections `g` and `h` is a corollary of applying `sum_rearrange_Icc_left` twice.
-/
theorem sum_rearrange_Icc {n:ℕ} {X':Type*} (X: Finset X') (hcard: X.card = n) (f: X' → ℝ) (g h: ℤ → X')
  (hg : ∀ i ∈ Icc (1:ℤ) n, g i ∈ X)
  (hh : ∀ i ∈ Icc (1:ℤ) n, h i ∈ X)
  (ginj: Function.Injective ((Icc (1:ℤ) n).restrict g))
  (hinj: Function.Injective ((Icc (1:ℤ) n).restrict h)) :
    ∑ i ∈ Icc (1:ℤ) n, f (g i) = ∑ i ∈ Icc (1:ℤ) n, f (h i) := by
  sorry

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
  sorry

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
  sorry

/-
This is another standard Finset induction proof.

Hints:
1. Start with `simp_rw [Pi.add_apply]` followed by `induction X using Finset.induction`
-/
theorem _sum_add_distrib {X':Type*} [DecidableEq X'] (f g: X' → ℝ) (X: Finset X') :
    ∑ x ∈ X, (f + g) x = ∑ x ∈ X, f x + ∑ x ∈ X, g x := by
  sorry

/-
Keyword: Finset induction.
-/
theorem _sum_mul {X':Type*} [DecidableEq X'] (f: X' → ℝ) (X: Finset X') (c:ℝ) :
    ∑ x ∈ X, c * f x = c * ∑ x ∈ X, f x := by
  sorry

/-
You guessed it, Finset induction!
-/
theorem _sum_le_sum {X':Type*} [DecidableEq X'] (f g: X' → ℝ) (X: Finset X') (h: ∀ x ∈ X, f x ≤ g x) :
    ∑ x ∈ X, f x ≤ ∑ x ∈ X, g x := by
  sorry

/-
`abs_finite_series_le` + Finset induction.
-/
theorem _abs_sum_le_sum_abs {X':Type*} [DecidableEq X'] (f: X' → ℝ) (X: Finset X') :
    |∑ x ∈ X, f x| ≤ ∑ x ∈ X, |f x| := by
  sorry

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
  sorry

/-
This is "Fubini's theorem for sums". Cartesian product flavor.
The proof is simple using another formulation of rearrangement called `sum_nbij`.
Start with `apply sum_nbij (i := Prod.swap)`.
-/
theorem sum_product_comm {XX YY:Type*} [DecidableEq XX] [DecidableEq YY] (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ z ∈ X ×ˢ Y, f z = ∑ z ∈ Y ×ˢ X, f (z.2, z.1) := by
  sorry

/-
This is Fubini for nested sums.
-/
theorem _sum_comm {XX YY:Type*} [DecidableEq XX] [DecidableEq YY] (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ y ∈ Y, ∑ x ∈ X, f (x, y) := by
  sorry

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
  sorry

-- `hi` is equivalent with `Set.MapsTo i s t` which means that `hi, i_inj, i_surj` are exactly `Set.BijOn i s t`
example : (∀ a ∈ s, i a ∈ t) ↔ Set.MapsTo i s t := Iff.rfl

/-
This is an immediate consequence of `sum_nbij`. Start with `symm` followed by `apply sum_nbij g`.
-/
theorem map_finite_series {X Y:Type*} [Fintype X] [Fintype Y] (f: X → ℝ) {g:Y → X}
  (hg: Function.Bijective g) :
    ∑ x, f x = ∑ y, f (g y) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

theorem sum_finite_col_row_counts {n m : ℕ} (a : Fin n → Fin m) :
    ∑ i, (a i : ℕ) = ∑ j : Fin m, #{i : Fin n | j < a i}.toFinset := by
  sorry

end challenges
