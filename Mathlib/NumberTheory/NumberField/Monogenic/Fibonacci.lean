/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.RootOfUnity
public import Mathlib.RingTheory.Polynomial.Dickson

/-!
# Monogenity of the factors of Fibonacci, Lucas and Chebyshev polynomials

Chen, Guo and Hong proved that every irreducible factor of the Fibonacci polynomial `Fₙ` is
monogenic when `n` is odd, and every irreducible factor of the Lucas polynomial `Lₙ` is
monogenic when `n` is even.

No new polynomial family is introduced here: the Fibonacci and Lucas polynomials are already
in Mathlib as **Dickson polynomials**.  Indeed the `(k, t)`-Fibonacci and `(k, t)`-Lucas
polynomials, defined by `F₀ = 0`, `F₁ = 1`, `Fₙ₊₂ = k X Fₙ₊₁ + t Fₙ` and `L₀ = 2`,
`L₁ = k X`, `Lₙ₊₂ = k X Lₙ₊₁ + t Lₙ`, satisfy
`Fₙ₊₁ = (dickson 2 (-t) n).comp (C k * X)` and `Lₙ = (dickson 1 (-t) n).comp (C k * X)`
(`Polynomial.eq_dickson_two_comp_of_rec`, `Polynomial.eq_dickson_one_comp_of_rec`); and at
`t = -1` Mathlib already identifies `dickson 2 1 = Chebyshev.S`, `dickson 1 1 = Chebyshev.C`
and `Chebyshev.U n = (dickson 2 1 n).comp (2 * X)`.  So the whole `(k, t)`-family is the
Dickson family up to the substitution `X ↦ k X`, and the polynomial sequences are carried by
their defining recurrences as hypotheses.

## Main results

* `Polynomial.dickson_one_eval`, `Polynomial.dickson_two_eval`: Binet's formulas for the
  Dickson polynomials of the first and second kind.  The first generalises Mathlib's
  `Polynomial.dickson_one_one_eval_add_inv` from `a = 1` to an arbitrary parameter `a`.
* `Polynomial.monogenic_of_isRoot_dickson_two_neg_one`,
  `Polynomial.monogenic_of_isRoot_dickson_one_neg_one`: the ring of integers of `ℚ(x)` is
  `ℤ[x]` for every root `x` of `dickson 2 (-1) m` (`m` even) resp. `dickson 1 (-1) m`
  (`m` even, nonzero).  Restated for the Fibonacci and Lucas polynomials themselves these
  are `Polynomial.monogenic_of_isRoot_fibonacci` and `Polynomial.monogenic_of_isRoot_lucas`,
  i.e. Theorems 1.1 and 1.2 of Chen–Guo–Hong.
* `Polynomial.monogenic_of_isRoot_dickson_two_one`,
  `Polynomial.monogenic_of_isRoot_dickson_one_one`: the parameter `a = 1` analogues, valid
  for **every** `m` — the roots now generate subfields of the maximal *real* subfield of a
  cyclotomic field.  Via Mathlib's bridges these say that every irreducible factor of a
  Chebyshev polynomial `S`, `C` or `U` is monogenic
  (`Polynomial.monogenic_of_isRoot_chebyshev_S` and companions).  These are new.

## Strategy

Write `α, β` for the roots of the characteristic polynomial `Y ^ 2 - x Y + a`, so that
`α + β = x` and `α β = a`.  Binet's formulas give
`(α - β) (dickson 2 a m)(x) = α ^ (m + 1) - β ^ (m + 1)` and
`(dickson 1 a m)(x) = α ^ m + β ^ m`.  If `x` is a root then `α ^ (2 (m + 1)) = a ^ (m + 1)`,
resp. `α ^ (2 m) = -a ^ m`.  So for `a = ±1` the element `α` is a root of unity and `x` is
`α - α⁻¹` (when `a = -1`) or `α + α⁻¹` (when `a = 1`).  The degenerate case `α = β` is
excluded because there `α (dickson 2 a m)(x) = (m + 1) α ^ (m + 1)` and
`(dickson 1 a m)(x) = 2 α ^ m` are nonzero.  The conclusion is then the theorem on
`ℤ[ζ ± ζ⁻¹]` of `Mathlib/NumberTheory/NumberField/Monogenic/RootOfUnity.lean`.
-/

@[expose] public section

noncomputable section

open Polynomial IntermediateField

namespace Polynomial

/-! ### Binet's formulas for Dickson polynomials -/

section Binet

variable {R : Type*} [CommRing R] {a x α β : R}

/-- **Binet's formula for Dickson polynomials of the first kind.**  If `α + β = x` and
`α β = a` then `(dickson 1 a n)(x) = αⁿ + βⁿ`.

This generalises `Polynomial.dickson_one_one_eval_add_inv`, which is the case `a = 1`. -/
theorem dickson_one_eval (hs : α + β = x) (hp : α * β = a) :
    ∀ n : ℕ, (dickson 1 a n).eval x = α ^ n + β ^ n
  | 0 => by simp only [dickson_zero]; norm_num
  | 1 => by simp only [dickson_one, eval_X, pow_one]; exact hs.symm
  | n + 2 => by
    have ih2 := dickson_one_eval hs hp (n + 1)
    have ih1 := dickson_one_eval hs hp n
    rw [dickson_add_two, eval_sub, eval_mul, eval_mul, eval_X, eval_C]
    linear_combination x * ih2 - a * ih1 - (α ^ (n + 1) + β ^ (n + 1)) * hs + (α ^ n + β ^ n) * hp

/-- **Binet's formula for Dickson polynomials of the second kind.**  If `α + β = x` and
`α β = a` then `(α - β) (dickson 2 a n)(x) = α ^ (n + 1) - β ^ (n + 1)`. -/
theorem dickson_two_eval (hs : α + β = x) (hp : α * β = a) :
    ∀ n : ℕ, (α - β) * (dickson 2 a n).eval x = α ^ (n + 1) - β ^ (n + 1)
  | 0 => by simp only [dickson_zero]; norm_num
  | 1 => by
    simp only [dickson_one, eval_X]
    linear_combination (β - α) * hs
  | n + 2 => by
    have ih2 := dickson_two_eval hs hp (n + 1)
    have ih1 := dickson_two_eval hs hp n
    rw [dickson_add_two, eval_sub, eval_mul, eval_mul, eval_X, eval_C]
    linear_combination x * ih2 - a * ih1 - (α ^ (n + 2) - β ^ (n + 2)) * hs
      + (α ^ (n + 1) - β ^ (n + 1)) * hp

/-- The degenerate case of Binet's formula for the first kind: if the characteristic
polynomial has the double root `α`, then `(dickson 1 a n)(x) = 2 αⁿ`. -/
theorem dickson_one_eval_of_double (hs : α + α = x) (hp : α * α = a) :
    ∀ n : ℕ, (dickson 1 a n).eval x = 2 * α ^ n
  | 0 => by simp only [dickson_zero]; norm_num
  | 1 => by
    simp only [dickson_one, eval_X, pow_one]
    linear_combination -hs
  | n + 2 => by
    have ih2 := dickson_one_eval_of_double hs hp (n + 1)
    have ih1 := dickson_one_eval_of_double hs hp n
    rw [dickson_add_two, eval_sub, eval_mul, eval_mul, eval_X, eval_C]
    linear_combination x * ih2 - a * ih1 - 2 * α ^ (n + 1) * hs + 2 * α ^ n * hp

/-- The degenerate case of Binet's formula for the second kind:
`α (dickson 2 a n)(x) = (n + 1) α ^ (n + 1)`. -/
theorem dickson_two_eval_of_double (hs : α + α = x) (hp : α * α = a) :
    ∀ n : ℕ, α * (dickson 2 a n).eval x = ((n : R) + 1) * α ^ (n + 1)
  | 0 => by simp only [dickson_zero]; norm_num
  | 1 => by
    simp only [dickson_one, eval_X]
    push_cast
    linear_combination -α * hs
  | n + 2 => by
    have ih2 := dickson_two_eval_of_double hs hp (n + 1)
    have ih1 := dickson_two_eval_of_double hs hp n
    rw [dickson_add_two, eval_sub, eval_mul, eval_mul, eval_X, eval_C]
    push_cast at ih1 ih2 ⊢
    linear_combination x * ih2 - a * ih1 - ((n : R) + 2) * α ^ (n + 2) * hs
      + ((n : R) + 1) * α ^ (n + 1) * hp

end Binet

/-! ### Recognising the Fibonacci and Lucas recurrences

Following the style of `Mathlib/Analysis/Polynomial/KTFibonacciAnnulus.lean`, the
`(k, t)`-Fibonacci and `(k, t)`-Lucas polynomials are carried by their defining recurrences
rather than defined afresh; these lemmas identify them with Dickson polynomials. -/

section Recurrence

variable {R : Type*} [CommRing R] {a k : R} {D : ℕ → R[X]}

/-- A sequence with `D 0 = 2`, `D 1 = k X` and `D (n + 2) = k X D (n + 1) - a D n` is the
sequence of Dickson polynomials of the first kind, rescaled by `X ↦ k X`.  With `k = 1` and
`a = -t` this says that the `(1, t)`-Lucas polynomials are `dickson 1 (-t)`. -/
theorem eq_dickson_one_comp_of_rec (h0 : D 0 = 2) (h1 : D 1 = C k * X)
    (hrec : ∀ n, D (n + 2) = C k * X * D (n + 1) - C a * D n) :
    ∀ n, D n = (dickson 1 a n).comp (C k * X)
  | 0 => by rw [h0, dickson_zero]; norm_num
  | 1 => by rw [h1, dickson_one, X_comp]
  | n + 2 => by
    rw [hrec, dickson_add_two, sub_comp, mul_comp, mul_comp, X_comp, C_comp,
      eq_dickson_one_comp_of_rec h0 h1 hrec (n + 1), eq_dickson_one_comp_of_rec h0 h1 hrec n]

/-- A sequence with `D 0 = 0`, `D 1 = 1` and `D (n + 2) = k X D (n + 1) - a D n` has
`D (n + 1)` equal to the `n`-th Dickson polynomial of the second kind, rescaled by
`X ↦ k X`.  With `k = 1` and `a = -t` this says that the `(1, t)`-Fibonacci polynomials
satisfy `Fₙ₊₁ = dickson 2 (-t) n`. -/
theorem eq_dickson_two_comp_of_rec (h0 : D 0 = 0) (h1 : D 1 = 1)
    (hrec : ∀ n, D (n + 2) = C k * X * D (n + 1) - C a * D n) :
    ∀ n, D (n + 1) = (dickson 2 a n).comp (C k * X)
  | 0 => by rw [h1, dickson_zero]; norm_num
  | 1 => by rw [hrec, h1, h0, dickson_one, X_comp]; ring
  | n + 2 => by
    rw [hrec (n + 1), dickson_add_two, sub_comp, mul_comp, mul_comp, X_comp, C_comp,
      eq_dickson_two_comp_of_rec h0 h1 hrec (n + 1), eq_dickson_two_comp_of_rec h0 h1 hrec n]

end Recurrence

/-! ### The characteristic polynomial of a root -/

section Roots

variable {L : Type*} [Field L] [CharZero L] {a x α : L}

omit [CharZero L] in
lemma char_sum (x α : L) : α + (x - α) = x := by ring

omit [CharZero L] in
lemma char_prod (hα : α ^ 2 - x * α + a = 0) : α * (x - α) = a := by linear_combination -hα

omit [CharZero L] in
lemma char_ne_zero (hα : α ^ 2 - x * α + a = 0) (ha : a ≠ 0) : α ≠ 0 := by
  intro h0
  rw [h0] at hα
  exact ha (by linear_combination hα)

/-- In characteristic zero a root of `dickson 2 a m` has a separable characteristic
polynomial: a double root `α` would force `(m + 1) α ^ (m + 1) = 0`. -/
lemma char_ne_of_isRoot_dickson_two {m : ℕ} (hα : α ^ 2 - x * α + a = 0) (ha : a ≠ 0)
    (hx : (dickson 2 a m).eval x = 0) : x - α ≠ α := by
  intro h
  have hα0 : α ≠ 0 := char_ne_zero hα ha
  have hs : α + α = x := by linear_combination -h
  have hp : α * α = a := by rw [← char_prod hα, h]
  have hkey := dickson_two_eval_of_double hs hp m
  rw [hx, mul_zero] at hkey
  rcases mul_eq_zero.mp hkey.symm with h' | h'
  · rw [show ((m : L) + 1) = ((m + 1 : ℕ) : L) by push_cast; ring] at h'
    exact absurd (Nat.cast_eq_zero.mp h') (by omega)
  · exact hα0 (pow_eq_zero_iff'.mp h').1

/-- The analogue for the first kind: a double root would force `2 αᵐ = 0`. -/
lemma char_ne_of_isRoot_dickson_one {m : ℕ} (hα : α ^ 2 - x * α + a = 0) (ha : a ≠ 0)
    (hx : (dickson 1 a m).eval x = 0) : x - α ≠ α := by
  intro h
  have hα0 : α ≠ 0 := char_ne_zero hα ha
  have hs : α + α = x := by linear_combination -h
  have hp : α * α = a := by rw [← char_prod hα, h]
  have hkey := dickson_one_eval_of_double hs hp m
  rw [hx] at hkey
  rcases mul_eq_zero.mp hkey.symm with h' | h'
  · exact absurd h' two_ne_zero
  · exact hα0 (pow_eq_zero_iff'.mp h').1

end Roots

/-! ### Roots of unity attached to the roots -/

section RootsOfUnity

variable {L : Type*} [Field L] [CharZero L] {α : L}

omit [CharZero L] in
/-- An element of finite order is an algebraic integer. -/
lemma isIntegral_of_pow_eq_one {N : ℕ} (hN : N ≠ 0) (h : α ^ N = 1) : IsIntegral ℤ α :=
  ⟨X ^ N - 1, monic_X_pow_sub_C 1 hN, by simp [h]⟩

omit [CharZero L] in
/-- If `α` has finite order then so does `α⁻¹`. -/
lemma isIntegral_inv_of_pow_eq_one {N : ℕ} (hN : N ≠ 0) (h : α ^ N = 1) : IsIntegral ℤ α⁻¹ :=
  isIntegral_of_pow_eq_one hN (by rw [inv_pow, h, inv_one])

/-- `2 n - 1` is coprime to every divisor of `4 n`. -/
private lemma coprime_two_mul_sub_one {n m : ℕ} (hn : n ≠ 0) (hm : m ∣ 4 * n) :
    Nat.Coprime (2 * n - 1) m := by
  have hd1 : Nat.gcd (2 * n - 1) m ∣ 2 * n - 1 := Nat.gcd_dvd_left _ _
  have hd2 : Nat.gcd (2 * n - 1) m ∣ 4 * n := (Nat.gcd_dvd_right _ _).trans hm
  have hodd : ¬ (2 ∣ Nat.gcd (2 * n - 1) m) := fun h => by
    have := h.trans hd1
    omega
  have h2 : Nat.Coprime (Nat.gcd (2 * n - 1) m) 2 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mpr hodd).symm
  have hc4 : Nat.Coprime (Nat.gcd (2 * n - 1) m) 4 := by
    simpa using h2.pow_right 2
  have hdn : Nat.gcd (2 * n - 1) m ∣ n := hc4.dvd_of_dvd_mul_left hd2
  have hone : Nat.gcd (2 * n - 1) m ∣ 1 := by
    have h2n : Nat.gcd (2 * n - 1) m ∣ 2 * n := hdn.mul_left 2
    have hsub := Nat.dvd_sub h2n hd1
    rwa [show 2 * n - (2 * n - 1) = 1 by omega] at hsub
  exact Nat.dvd_one.mp hone

/-- **The key structural statement.**  If `α ^ (2 n) = -1` (with `n ≠ 0`) and `-α⁻¹ ≠ α`,
then the ring of integers of `ℚ(α - α⁻¹)` is `ℤ[α - α⁻¹]`. -/
theorem mem_adjoin_int_sub_inv_of_pow_eq_neg_one {n : ℕ} (hn : n ≠ 0)
    (h2n : α ^ (2 * n) = -1) (hne : -α⁻¹ ≠ α)
    {y : L} (hy : IsIntegral ℤ y) (hymem : y ∈ ℚ⟮α - α⁻¹⟯) :
    y ∈ Algebra.adjoin ℤ ({α - α⁻¹} : Set L) := by
  have hα0 : α ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at h2n
    exact absurd h2n.symm (by norm_num)
  have h4n : α ^ (4 * n) = 1 := by
    rw [show 4 * n = 2 * n + 2 * n by ring, pow_add, h2n]
    ring
  have hm0 : orderOf α ≠ 0 := by
    have : IsOfFinOrder α := isOfFinOrder_iff_pow_eq_one.mpr ⟨4 * n, by omega, h4n⟩
    exact (orderOf_pos_iff.mpr this).ne'
  haveI : NeZero (orderOf α) := ⟨hm0⟩
  have hα : IsPrimitiveRoot α (orderOf α) := IsPrimitiveRoot.orderOf α
  have hdvd : orderOf α ∣ 4 * n := orderOf_dvd_of_pow_eq_one h4n
  have hpow : α ^ (2 * n - 1) = -α⁻¹ := by
    have h1 : α ^ (2 * n - 1) * α = -1 := by
      rw [← pow_succ, show 2 * n - 1 + 1 = 2 * n by omega]
      exact h2n
    field_simp
    linear_combination h1
  have hβ : IsPrimitiveRoot (-α⁻¹) (orderOf α) := by
    rw [← hpow]
    exact hα.pow_of_coprime _ (coprime_two_mul_sub_one hn hdvd)
  exact hα.mem_adjoin_int_sub_inv_of_neg_inv hβ hne hy hymem

/-- The companion statement for the *real* subfield: if `α` is a root of unity with
`α ^ 2 ≠ 1`, then the ring of integers of `ℚ(α + α⁻¹)` is `ℤ[α + α⁻¹]`. -/
theorem mem_adjoin_int_add_inv_of_pow_eq_one {N : ℕ} (hN : N ≠ 0)
    (hpow : α ^ N = 1) (hne : α ^ 2 ≠ 1)
    {y : L} (hy : IsIntegral ℤ y) (hymem : y ∈ ℚ⟮α + α⁻¹⟯) :
    y ∈ Algebra.adjoin ℤ ({α + α⁻¹} : Set L) := by
  have hm0 : orderOf α ≠ 0 := by
    have : IsOfFinOrder α := isOfFinOrder_iff_pow_eq_one.mpr ⟨N, Nat.pos_of_ne_zero hN, hpow⟩
    exact (orderOf_pos_iff.mpr this).ne'
  haveI : NeZero (orderOf α) := ⟨hm0⟩
  have hα : IsPrimitiveRoot α (orderOf α) := IsPrimitiveRoot.orderOf α
  have h2 : ¬ (orderOf α ∣ 2) := fun h => hne (orderOf_dvd_iff_pow_eq_one.mp h)
  have hgt : 2 < orderOf α := by
    by_contra hc
    have hcase : orderOf α = 1 ∨ orderOf α = 2 := by omega
    rcases hcase with h' | h' <;> rw [h'] at h2 <;> simp at h2
  exact hα.mem_adjoin_int_add_inv hgt hy hymem

end RootsOfUnity

/-! ### The main theorems -/

section Main

variable {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] {m : ℕ} {x α : L}

omit [CharZero L] [IsAlgClosed L] in
/-- Evaluating an integral Dickson polynomial in an algebra. -/
lemma aeval_dickson (k n : ℕ) (a : ℤ) (x : L) :
    aeval x (dickson k a n) = eval x (dickson k ((a : ℤ) : L) n) := by
  rw [aeval_def, eval₂_eq_eval_map, map_dickson]
  simp

omit [CharZero L] in
/-- A root of the characteristic polynomial `Y ^ 2 - x Y + a` exists. -/
private lemma exists_char_root (a x : L) : ∃ α : L, α ^ 2 - x * α + a = 0 := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (C (1 : L) * X ^ 2 + C (-x) * X + C a)
    (by rw [degree_quadratic one_ne_zero]; norm_num)
  refine ⟨α, ?_⟩
  simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hα
  linear_combination hα

omit [IsAlgClosed L] in
/-- With `a = -1`: `x = α - α⁻¹` and `-α⁻¹ ≠ α`. -/
private lemma sub_inv_data (hα : α ^ 2 - x * α + (-1 : L) = 0) (hne : x - α ≠ α) :
    α ≠ 0 ∧ x - α = -α⁻¹ ∧ x = α - α⁻¹ ∧ -α⁻¹ ≠ α := by
  have hα0 : α ≠ 0 := char_ne_zero hα (by norm_num)
  have hp := char_prod hα
  have hβ : x - α = -α⁻¹ := by field_simp; linear_combination hp
  refine ⟨hα0, hβ, ?_, hβ ▸ hne⟩
  have h := char_sum x α
  rw [hβ] at h
  rw [← h]; ring

omit [IsAlgClosed L] in
/-- With `a = 1`: `x = α + α⁻¹` and `α ^ 2 ≠ 1`. -/
private lemma add_inv_data (hα : α ^ 2 - x * α + (1 : L) = 0) (hne : x - α ≠ α) :
    α ≠ 0 ∧ x - α = α⁻¹ ∧ x = α + α⁻¹ ∧ α ^ 2 ≠ 1 := by
  have hα0 : α ≠ 0 := char_ne_zero hα one_ne_zero
  have hp := char_prod hα
  have hβ : x - α = α⁻¹ := by field_simp; linear_combination hp
  refine ⟨hα0, hβ, ?_, ?_⟩
  · have h := char_sum x α
    rw [hβ] at h
    rw [← h]
  · intro h
    exact hne (by rw [hβ]; field_simp; linear_combination -h)

/-- **Theorem 1.1 of Chen–Guo–Hong**, for Dickson polynomials of the second kind: for `m`
even, every root `x` of `dickson 2 (-1) m` is an algebraic integer with `𝓞 ℚ(x) = ℤ[x]`.

Since the `n`-th Fibonacci polynomial is `dickson 2 (-1) (n - 1)`, this is the statement for
odd-indexed Fibonacci polynomials; see `Polynomial.monogenic_of_isRoot_fibonacci`. -/
theorem monogenic_of_isRoot_dickson_two_neg_one (hm : Even m)
    (hx : aeval x (dickson 2 (-1 : ℤ) m) = 0) :
    IsIntegral ℤ x ∧ ∀ y ∈ ℚ⟮x⟯, IsIntegral ℤ y → y ∈ Algebra.adjoin ℤ ({x} : Set L) := by
  rw [aeval_dickson] at hx
  push_cast at hx
  obtain ⟨α, hα⟩ := exists_char_root (-1 : L) x
  have hne := char_ne_of_isRoot_dickson_two hα (by norm_num) hx
  obtain ⟨hα0, hβ, hxeq, hne'⟩ := sub_inv_data hα hne
  have hp := char_prod hα
  have hbin := dickson_two_eval (char_sum x α) hp m
  rw [hx, mul_zero] at hbin
  have h2n : α ^ (2 * (m + 1)) = -1 := by
    have h1 : α ^ (m + 1) * α ^ (m + 1) = α ^ (m + 1) * (x - α) ^ (m + 1) := by
      rw [← sub_eq_zero] at hbin ⊢
      linear_combination -(α ^ (m + 1)) * hbin
    rw [two_mul, pow_add, h1, ← mul_pow, hp]
    exact (Even.add_one hm).neg_one_pow
  have h4n : α ^ (4 * (m + 1)) = 1 := by
    rw [show 4 * (m + 1) = 2 * (m + 1) + 2 * (m + 1) by ring, pow_add, h2n]; ring
  refine ⟨hxeq ▸ (isIntegral_of_pow_eq_one (N := 4 * (m + 1)) (by omega) h4n).sub
      (isIntegral_inv_of_pow_eq_one (N := 4 * (m + 1)) (by omega) h4n), fun y hymem hy => ?_⟩
  rw [hxeq] at hymem ⊢
  exact mem_adjoin_int_sub_inv_of_pow_eq_neg_one (by omega) h2n hne' hy hymem

/-- **Theorem 1.2 of Chen–Guo–Hong**, for Dickson polynomials of the first kind: for `m`
even and nonzero, every root `x` of `dickson 1 (-1) m` is an algebraic integer with
`𝓞 ℚ(x) = ℤ[x]`.  See `Polynomial.monogenic_of_isRoot_lucas`. -/
theorem monogenic_of_isRoot_dickson_one_neg_one (hm : Even m) (hm0 : m ≠ 0)
    (hx : aeval x (dickson 1 (-1 : ℤ) m) = 0) :
    IsIntegral ℤ x ∧ ∀ y ∈ ℚ⟮x⟯, IsIntegral ℤ y → y ∈ Algebra.adjoin ℤ ({x} : Set L) := by
  rw [aeval_dickson] at hx
  push_cast at hx
  obtain ⟨α, hα⟩ := exists_char_root (-1 : L) x
  have hne := char_ne_of_isRoot_dickson_one hα (by norm_num) hx
  obtain ⟨hα0, hβ, hxeq, hne'⟩ := sub_inv_data hα hne
  have hp := char_prod hα
  have hbin := dickson_one_eval (char_sum x α) hp m
  rw [hx] at hbin
  have h2n : α ^ (2 * m) = -1 := by
    have h1 : α ^ m * α ^ m = -(α ^ m * (x - α) ^ m) := by
      rw [← sub_eq_zero]
      linear_combination α ^ m * hbin.symm
    rw [two_mul, pow_add, h1, ← mul_pow, hp, hm.neg_one_pow]
  have h4n : α ^ (4 * m) = 1 := by
    rw [show 4 * m = 2 * m + 2 * m by ring, pow_add, h2n]; ring
  refine ⟨hxeq ▸ (isIntegral_of_pow_eq_one (N := 4 * m) (by omega) h4n).sub
      (isIntegral_inv_of_pow_eq_one (N := 4 * m) (by omega) h4n), fun y hymem hy => ?_⟩
  rw [hxeq] at hymem ⊢
  exact mem_adjoin_int_sub_inv_of_pow_eq_neg_one hm0 h2n hne' hy hymem

/-- **The `a = 1` analogue of Theorem 1.1, with no parity restriction.**  Every root of
`dickson 2 1 m = Chebyshev.S m` generates a monogenic field. -/
theorem monogenic_of_isRoot_dickson_two_one (hx : aeval x (dickson 2 (1 : ℤ) m) = 0) :
    IsIntegral ℤ x ∧ ∀ y ∈ ℚ⟮x⟯, IsIntegral ℤ y → y ∈ Algebra.adjoin ℤ ({x} : Set L) := by
  rw [aeval_dickson] at hx
  push_cast at hx
  obtain ⟨α, hα⟩ := exists_char_root (1 : L) x
  have hne := char_ne_of_isRoot_dickson_two hα one_ne_zero hx
  obtain ⟨hα0, hβ, hxeq, hsq⟩ := add_inv_data hα hne
  have hp := char_prod hα
  have hbin := dickson_two_eval (char_sum x α) hp m
  rw [hx, mul_zero] at hbin
  have h2n : α ^ (2 * (m + 1)) = 1 := by
    have h1 : α ^ (m + 1) * α ^ (m + 1) = α ^ (m + 1) * (x - α) ^ (m + 1) := by
      rw [← sub_eq_zero] at hbin ⊢
      linear_combination -(α ^ (m + 1)) * hbin
    rw [two_mul, pow_add, h1, ← mul_pow, hp, one_pow]
  refine ⟨hxeq ▸ (isIntegral_of_pow_eq_one (N := 2 * (m + 1)) (by omega) h2n).add
      (isIntegral_inv_of_pow_eq_one (N := 2 * (m + 1)) (by omega) h2n), fun y hymem hy => ?_⟩
  rw [hxeq] at hymem ⊢
  exact mem_adjoin_int_add_inv_of_pow_eq_one (by omega) h2n hsq hy hymem

/-- **The `a = 1` analogue of Theorem 1.2, with no parity restriction.**  Every root of
`dickson 1 1 m = Chebyshev.C m` (`m ≠ 0`) generates a monogenic field. -/
theorem monogenic_of_isRoot_dickson_one_one (hm0 : m ≠ 0)
    (hx : aeval x (dickson 1 (1 : ℤ) m) = 0) :
    IsIntegral ℤ x ∧ ∀ y ∈ ℚ⟮x⟯, IsIntegral ℤ y → y ∈ Algebra.adjoin ℤ ({x} : Set L) := by
  rw [aeval_dickson] at hx
  push_cast at hx
  obtain ⟨α, hα⟩ := exists_char_root (1 : L) x
  have hne := char_ne_of_isRoot_dickson_one hα one_ne_zero hx
  obtain ⟨hα0, hβ, hxeq, hsq⟩ := add_inv_data hα hne
  have hp := char_prod hα
  have hbin := dickson_one_eval (char_sum x α) hp m
  rw [hx] at hbin
  have h2n : α ^ (2 * m) = -1 := by
    have h1 : α ^ m * α ^ m = -(α ^ m * (x - α) ^ m) := by
      rw [← sub_eq_zero]
      linear_combination α ^ m * hbin.symm
    rw [two_mul, pow_add, h1, ← mul_pow, hp, one_pow]
  have h4n : α ^ (4 * m) = 1 := by
    rw [show 4 * m = 2 * m + 2 * m by ring, pow_add, h2n]; ring
  refine ⟨hxeq ▸ (isIntegral_of_pow_eq_one (N := 4 * m) (by omega) h4n).add
      (isIntegral_inv_of_pow_eq_one (N := 4 * m) (by omega) h4n), fun y hymem hy => ?_⟩
  rw [hxeq] at hymem ⊢
  exact mem_adjoin_int_add_inv_of_pow_eq_one (by omega) h4n hsq hy hymem

/-! ### The theorems in the standard `𝓞 K = ℤ[θ]` form -/

open NumberField in
/-- Theorem 1.1 restated: `ℤ[θ] = 𝓞 ℚ(x)` for any `θ` lying over a root `x`. -/
theorem adjoin_eq_top_of_isRoot_dickson_two_neg_one (hm : Even m)
    (hx : aeval x (dickson 2 (-1 : ℤ) m) = 0) {θ : 𝓞 ℚ⟮x⟯}
    (hθ : (algebraMap (𝓞 ℚ⟮x⟯) ℚ⟮x⟯ θ : L) = x) :
    Algebra.adjoin ℤ ({θ} : Set (𝓞 ℚ⟮x⟯)) = ⊤ :=
  Monogenic.adjoin_eq_top_of_forall_mem hθ (monogenic_of_isRoot_dickson_two_neg_one hm hx).2

open NumberField in
/-- Theorem 1.2 restated. -/
theorem adjoin_eq_top_of_isRoot_dickson_one_neg_one (hm : Even m) (hm0 : m ≠ 0)
    (hx : aeval x (dickson 1 (-1 : ℤ) m) = 0) {θ : 𝓞 ℚ⟮x⟯}
    (hθ : (algebraMap (𝓞 ℚ⟮x⟯) ℚ⟮x⟯ θ : L) = x) :
    Algebra.adjoin ℤ ({θ} : Set (𝓞 ℚ⟮x⟯)) = ⊤ :=
  Monogenic.adjoin_eq_top_of_forall_mem hθ
    (monogenic_of_isRoot_dickson_one_neg_one hm hm0 hx).2

open NumberField in
/-- The `a = 1` analogue restated. -/
theorem adjoin_eq_top_of_isRoot_dickson_two_one (hx : aeval x (dickson 2 (1 : ℤ) m) = 0)
    {θ : 𝓞 ℚ⟮x⟯} (hθ : (algebraMap (𝓞 ℚ⟮x⟯) ℚ⟮x⟯ θ : L) = x) :
    Algebra.adjoin ℤ ({θ} : Set (𝓞 ℚ⟮x⟯)) = ⊤ :=
  Monogenic.adjoin_eq_top_of_forall_mem hθ (monogenic_of_isRoot_dickson_two_one hx).2

open NumberField in
/-- The `a = 1` analogue for the first kind, restated. -/
theorem adjoin_eq_top_of_isRoot_dickson_one_one (hm0 : m ≠ 0)
    (hx : aeval x (dickson 1 (1 : ℤ) m) = 0) {θ : 𝓞 ℚ⟮x⟯}
    (hθ : (algebraMap (𝓞 ℚ⟮x⟯) ℚ⟮x⟯ θ : L) = x) :
    Algebra.adjoin ℤ ({θ} : Set (𝓞 ℚ⟮x⟯)) = ⊤ :=
  Monogenic.adjoin_eq_top_of_forall_mem hθ (monogenic_of_isRoot_dickson_one_one hm0 hx).2

end Main

/-! ### Fibonacci, Lucas and Chebyshev polynomials

The polynomial families are carried by their defining recurrences; no new definition is
made. -/

section Named

variable {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] {n : ℕ} {x : L}

omit [CharZero L] [IsAlgClosed L] in
/-- A root of `p.comp (C k * X)` gives the root `k x` of `p`. -/
lemma aeval_of_aeval_comp {p : ℤ[X]} {k : ℤ} (hx : aeval x (p.comp (C k * X)) = 0) :
    aeval ((k : L) * x) p = 0 := by
  rwa [aeval_comp, map_mul, aeval_C, aeval_X, algebraMap_int_eq, eq_intCast] at hx

/-- **Theorem 1.1 (Chen–Guo–Hong), with the `(k, t)`-generalisation in `k`.**  Let `F` be any
sequence of integer polynomials with `F 0 = 0`, `F 1 = 1` and
`F (j + 2) = k X F (j + 1) + F j`, i.e. the `(k, 1)`-Fibonacci polynomials.  For `n` odd and
every root `x` of `F n`, the element `k x` is an algebraic integer and the ring of integers
of `ℚ(k x)` is `ℤ[k x]`.

For `k = 1` this says exactly that every irreducible factor of an odd-indexed Fibonacci
polynomial is monogenic. -/
theorem monogenic_of_isRoot_fibonacci {k : ℤ} {F : ℕ → ℤ[X]} (h0 : F 0 = 0) (h1 : F 1 = 1)
    (hrec : ∀ j, F (j + 2) = C k * X * F (j + 1) + F j) (hn : Odd n)
    (hx : aeval x (F n) = 0) :
    IsIntegral ℤ ((k : L) * x) ∧ ∀ y ∈ ℚ⟮(k : L) * x⟯, IsIntegral ℤ y →
      y ∈ Algebra.adjoin ℤ ({(k : L) * x} : Set L) := by
  obtain ⟨j, rfl⟩ := hn
  have hF := eq_dickson_two_comp_of_rec (a := -1) (k := k) h0 h1
    (fun i => by rw [hrec i, C_neg, C_1]; ring) (2 * j)
  rw [hF] at hx
  exact monogenic_of_isRoot_dickson_two_neg_one (m := 2 * j) ⟨j, by ring⟩
    (aeval_of_aeval_comp hx)

/-- **Theorem 1.2 (Chen–Guo–Hong), with the `(k, t)`-generalisation in `k`.**  The Lucas
analogue: `Lu 0 = 2`, `Lu 1 = k X`, `Lu (j + 2) = k X Lu (j + 1) + Lu j`, and `n` even and
nonzero. -/
theorem monogenic_of_isRoot_lucas {k : ℤ} {Lu : ℕ → ℤ[X]} (h0 : Lu 0 = 2) (h1 : Lu 1 = C k * X)
    (hrec : ∀ j, Lu (j + 2) = C k * X * Lu (j + 1) + Lu j) (hn : Even n) (hn0 : n ≠ 0)
    (hx : aeval x (Lu n) = 0) :
    IsIntegral ℤ ((k : L) * x) ∧ ∀ y ∈ ℚ⟮(k : L) * x⟯, IsIntegral ℤ y →
      y ∈ Algebra.adjoin ℤ ({(k : L) * x} : Set L) := by
  have hL := eq_dickson_one_comp_of_rec (a := -1) (k := k) h0 h1
    (fun i => by rw [hrec i, C_neg, C_1]; ring) n
  rw [hL] at hx
  exact monogenic_of_isRoot_dickson_one_neg_one (m := n) hn hn0 (aeval_of_aeval_comp hx)

/-- Every irreducible factor of the Chebyshev polynomial `S n` is monogenic. -/
theorem monogenic_of_isRoot_chebyshev_S (hx : aeval x (Chebyshev.S ℤ n) = 0) :
    IsIntegral ℤ x ∧ ∀ y ∈ ℚ⟮x⟯, IsIntegral ℤ y → y ∈ Algebra.adjoin ℤ ({x} : Set L) :=
  monogenic_of_isRoot_dickson_two_one (by rwa [dickson_two_one_eq_chebyshev_S])

/-- Every irreducible factor of the Chebyshev polynomial `C n` (`n ≠ 0`) is monogenic. -/
theorem monogenic_of_isRoot_chebyshev_C (hn0 : n ≠ 0) (hx : aeval x (Chebyshev.C ℤ n) = 0) :
    IsIntegral ℤ x ∧ ∀ y ∈ ℚ⟮x⟯, IsIntegral ℤ y → y ∈ Algebra.adjoin ℤ ({x} : Set L) :=
  monogenic_of_isRoot_dickson_one_one hn0 (by rwa [dickson_one_one_eq_chebyshev_C])

/-- Every irreducible factor of the Chebyshev polynomial `U n` of the second kind is
monogenic: `2 x` generates the ring of integers of `ℚ(x)`.  This is the case `k = 2` of the
`(k, t)`-family, via Mathlib's `Polynomial.chebyshev_U_eq_dickson_two_one`. -/
theorem monogenic_of_isRoot_chebyshev_U (hx : aeval x (Chebyshev.U ℤ n) = 0) :
    IsIntegral ℤ ((2 : L) * x) ∧ ∀ y ∈ ℚ⟮(2 : L) * x⟯, IsIntegral ℤ y →
      y ∈ Algebra.adjoin ℤ ({(2 : L) * x} : Set L) := by
  rw [chebyshev_U_eq_dickson_two_one, show (2 : ℤ[X]) = C (2 : ℤ) by simp] at hx
  have h := monogenic_of_isRoot_dickson_two_one (L := L) (aeval_of_aeval_comp hx)
  simpa using h

end Named

end Polynomial

end

end
