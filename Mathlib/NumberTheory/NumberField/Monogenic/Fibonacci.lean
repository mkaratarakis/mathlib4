/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.RootOfUnity

/-!
# Monogenity of the factors of Fibonacci and Lucas polynomials

The Fibonacci polynomials are `F₀ = 0`, `F₁ = 1`, `Fₙ₊₂ = X Fₙ₊₁ + Fₙ` and the Lucas
polynomials are `L₀ = 2`, `L₁ = X`, `Lₙ₊₂ = X Lₙ₊₁ + Lₙ`.  Chen, Guo and Hong proved that
every irreducible factor of `Fₙ` is monogenic when `n` is odd, and every irreducible factor
of `Lₙ` is monogenic when `n` is even.

This file works throughout with the `(k, t)`-generalisations
`Fₙ₊₂ = k X Fₙ₊₁ + t Fₙ` and `Lₙ₊₂ = k X Lₙ₊₁ + t Lₙ`,
which contain the classical polynomials at `(k, t) = (1, 1)` and, at `(k, t) = (1, -1)`, the
Chebyshev polynomials of the second and first kind.

## Main results

* `Polynomial.monogenic_of_isRoot_fibPoly`: for `n` odd, `x` is an algebraic integer and the
  ring of integers of `ℚ(x)` is `ℤ[x]`, for every root `x` of the `n`-th Fibonacci
  polynomial.  This is Theorem 1.1; `Polynomial.adjoin_eq_top_of_isRoot_fibPoly` restates it
  as `Algebra.adjoin ℤ {θ} = ⊤` in `𝓞 ℚ(x)`.
* `Polynomial.monogenic_of_isRoot_lucasPoly`: the same for `n` even and the `n`-th Lucas
  polynomial.  This is Theorem 1.2.
* `Polynomial.monogenic_of_isRoot_fibPoly_neg`,
  `Polynomial.monogenic_of_isRoot_lucasPoly_neg`: the `t = -1` analogues, valid for
  **every** `n ≥ 1` — the roots now generate subfields of the maximal *real* subfield of a
  cyclotomic field.  These are new: they say that every irreducible factor of a Chebyshev
  polynomial of the first or second kind is monogenic.
* `Polynomial.monogenic_of_isRoot_fibPoly_gen` and its three companions: the same statements
  for arbitrary `k`, for the generator `k x` of `ℚ(x)`.

## Strategy

Write `α, β` for the roots of the characteristic polynomial `Y ^ 2 - k x Y - t`, so that
`α + β = k x` and `α β = -t`.  A Binet-type identity (`Polynomial.aeval_fibPoly`,
`Polynomial.aeval_lucasPoly`) gives

  `(α - β) Fₙ(x) = αⁿ - βⁿ`,  `Lₙ(x) = αⁿ + βⁿ`.

If `x` is a root of `Fₙ` then `αⁿ = βⁿ`, hence `α ^ (2 n) = (α β) ^ n = (-t) ^ n`; if `x` is a
root of `Lₙ` then `α ^ (2 n) = -(-t) ^ n`.  So `α` is a root of unity, and `x = α + β` is
`α - α⁻¹` when `t = 1` and `α + α⁻¹` when `t = -1`.  The degenerate case `α = β` is excluded
because there `Fₙ(x) = n α ^ (n - 1)` and `Lₙ(x) = 2 α ^ n` are nonzero.  The conclusion is
then the theorem on `ℤ[ζ ± ζ⁻¹]` of
`Mathlib/NumberTheory/NumberField/Monogenic/RootOfUnity.lean`.
-/

@[expose] public section

noncomputable section

open Polynomial IntermediateField

namespace Polynomial

/-! ### The `(k, t)`-Fibonacci and `(k, t)`-Lucas polynomials -/

/-- The `(k, t)`-Fibonacci polynomials: `F₀ = 0`, `F₁ = 1`, `Fₙ₊₂ = k X Fₙ₊₁ + t Fₙ`.
The classical Fibonacci polynomials are the case `(k, t) = (1, 1)`. -/
def fibPoly (k t : ℤ) : ℕ → ℤ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => C k * X * fibPoly k t (n + 1) + C t * fibPoly k t n

/-- The `(k, t)`-Lucas polynomials: `L₀ = 2`, `L₁ = k X`, `Lₙ₊₂ = k X Lₙ₊₁ + t Lₙ`.
The classical Lucas polynomials are the case `(k, t) = (1, 1)`. -/
def lucasPoly (k t : ℤ) : ℕ → ℤ[X]
  | 0 => 2
  | 1 => C k * X
  | n + 2 => C k * X * lucasPoly k t (n + 1) + C t * lucasPoly k t n

variable (k t : ℤ)

@[simp] lemma fibPoly_zero : fibPoly k t 0 = 0 := rfl
@[simp] lemma fibPoly_one : fibPoly k t 1 = 1 := rfl

lemma fibPoly_add_two (n : ℕ) :
    fibPoly k t (n + 2) = C k * X * fibPoly k t (n + 1) + C t * fibPoly k t n := rfl

@[simp] lemma lucasPoly_zero : lucasPoly k t 0 = 2 := rfl
@[simp] lemma lucasPoly_one : lucasPoly k t 1 = C k * X := rfl

lemma lucasPoly_add_two (n : ℕ) :
    lucasPoly k t (n + 2) = C k * X * lucasPoly k t (n + 1) + C t * lucasPoly k t n := rfl

/-! ### Binet-type identities -/

section Binet

variable {R : Type*} [CommRing R] {k t : ℤ} {x α β : R}

/-- **Binet's formula for the `(k, t)`-Fibonacci polynomials.**  If `α + β = k x` and
`α β = -t`, then `(α - β) Fₙ(x) = αⁿ - βⁿ`. -/
theorem aeval_fibPoly (hs : α + β = (k : R) * x) (hp : α * β = -(t : R)) (n : ℕ) :
    (α - β) * aeval x (fibPoly k t n) = α ^ n - β ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    rw [fibPoly_add_two]
    simp only [map_add, map_mul, aeval_X, eq_intCast, map_intCast]
    have hT : ((t : ℤ) : R) = -(α * β) := by rw [hp]; ring
    rw [hT, ← hs]
    linear_combination (α + β) * ih2 - α * β * ih1

/-- **Binet's formula for the `(k, t)`-Lucas polynomials.**  If `α + β = k x` and `α β = -t`,
then `Lₙ(x) = αⁿ + βⁿ`. -/
theorem aeval_lucasPoly (hs : α + β = (k : R) * x) (hp : α * β = -(t : R)) (n : ℕ) :
    aeval x (lucasPoly k t n) = α ^ n + β ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp only [lucasPoly_zero, pow_zero, map_ofNat]; ring
  | one => simpa using hs.symm
  | more n ih1 ih2 =>
    rw [lucasPoly_add_two]
    simp only [map_add, map_mul, aeval_X, eq_intCast, map_intCast]
    have hT : ((t : ℤ) : R) = -(α * β) := by rw [hp]; ring
    rw [hT, ← hs]
    linear_combination (α + β) * ih2 - α * β * ih1

/-- The degenerate case of Binet's formula: if the characteristic polynomial has the double
root `α`, then `α Fₙ(x) = n αⁿ`. -/
theorem aeval_fibPoly_of_double_root (hs : α + α = (k : R) * x) (hp : α * α = -(t : R)) (n : ℕ) :
    α * aeval x (fibPoly k t n) = (n : R) * α ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    rw [fibPoly_add_two]
    simp only [map_add, map_mul, aeval_X, eq_intCast, map_intCast]
    have hT : ((t : ℤ) : R) = -(α * α) := by rw [hp]; ring
    rw [hT, ← hs]
    push_cast at ih1 ih2 ⊢
    linear_combination (α + α) * ih2 - α * α * ih1

/-- The degenerate case of Binet's formula for Lucas polynomials: `Lₙ(x) = 2 αⁿ`. -/
theorem aeval_lucasPoly_of_double_root (hs : α + α = (k : R) * x) (hp : α * α = -(t : R))
    (n : ℕ) : aeval x (lucasPoly k t n) = 2 * α ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp only [lucasPoly_zero, pow_zero, map_ofNat]; ring
  | one =>
    have h1 : aeval x (lucasPoly k t 1) = (k : R) * x := by
      simp only [lucasPoly_one, map_mul, aeval_X, eq_intCast, map_intCast]
    rw [h1, ← hs, pow_one]; ring
  | more n ih1 ih2 =>
    rw [lucasPoly_add_two]
    simp only [map_add, map_mul, aeval_X, eq_intCast, map_intCast]
    have hT : ((t : ℤ) : R) = -(α * α) := by rw [hp]; ring
    rw [hT, ← hs]
    linear_combination (α + α) * ih2 - α * α * ih1

end Binet

/-! ### Roots of the characteristic polynomial -/

section Roots

variable {L : Type*} [Field L] [CharZero L] {k t : ℤ} {x α : L}

omit [CharZero L] in
lemma char_sum (α : L) : α + ((k : L) * x - α) = (k : L) * x := by ring

omit [CharZero L] in
lemma char_prod (hα : α ^ 2 - (k : L) * x * α - (t : L) = 0) :
    α * ((k : L) * x - α) = -(t : L) := by linear_combination -hα

lemma char_ne_zero (hα : α ^ 2 - (k : L) * x * α - (t : L) = 0) (ht : t ≠ 0) : α ≠ 0 := by
  intro h0
  rw [h0] at hα
  have : ((t : ℤ) : L) = 0 := by linear_combination -hα
  exact ht (by exact_mod_cast this)

/-- In characteristic zero the characteristic polynomial of a root of `Fₙ` (`n ≥ 1`) has two
*distinct* roots: a double root `α` would force `n αⁿ = 0`. -/
lemma char_ne_of_isRoot_fibPoly {n : ℕ} (hn : n ≠ 0) (hα : α ^ 2 - (k : L) * x * α - (t : L) = 0)
    (ht : t ≠ 0) (hx : aeval x (fibPoly k t n) = 0) : (k : L) * x - α ≠ α := by
  intro h
  have hα0 : α ≠ 0 := char_ne_zero hα ht
  have hs : α + α = (k : L) * x := by linear_combination -h
  have hp : α * α = -(t : L) := by rw [← char_prod hα, h]
  have hkey := aeval_fibPoly_of_double_root hs hp n
  rw [hx, mul_zero] at hkey
  have hn0 : (n : L) = 0 := by
    rcases mul_eq_zero.mp hkey.symm with h' | h'
    · exact h'
    · exact absurd (pow_eq_zero_iff'.mp h').1 hα0
  exact hn (by exact_mod_cast hn0)

/-- The Lucas analogue: a double root `α` would force `2 αⁿ = 0`. -/
lemma char_ne_of_isRoot_lucasPoly {n : ℕ} (hα : α ^ 2 - (k : L) * x * α - (t : L) = 0)
    (ht : t ≠ 0) (hx : aeval x (lucasPoly k t n) = 0) : (k : L) * x - α ≠ α := by
  intro h
  have hα0 : α ≠ 0 := char_ne_zero hα ht
  have hs : α + α = (k : L) * x := by linear_combination -h
  have hp : α * α = -(t : L) := by rw [← char_prod hα, h]
  have h2 := aeval_lucasPoly_of_double_root hs hp n
  rw [hx] at h2
  rcases mul_eq_zero.mp h2.symm with h' | h'
  · exact absurd h' two_ne_zero
  · exact hα0 (pow_eq_zero_iff'.mp h').1

end Roots

/-! ### Roots of unity attached to the roots -/

section RootsOfUnity

variable {L : Type*} [Field L] [CharZero L] {α : L}

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
  have hdn : Nat.gcd (2 * n - 1) m ∣ n :=
    hc4.dvd_of_dvd_mul_left hd2
  have hone : Nat.gcd (2 * n - 1) m ∣ 1 := by
    have h2n : Nat.gcd (2 * n - 1) m ∣ 2 * n := hdn.mul_left 2
    have hsub := Nat.dvd_sub h2n hd1
    rwa [show 2 * n - (2 * n - 1) = 1 by omega] at hsub
  exact Nat.dvd_one.mp hone

omit [CharZero L] in
/-- An element of finite order is an algebraic integer. -/
lemma isIntegral_of_pow_eq_one {N : ℕ} (hN : N ≠ 0) (h : α ^ N = 1) : IsIntegral ℤ α :=
  ⟨X ^ N - 1, monic_X_pow_sub_C 1 hN, by simp [h]⟩

omit [CharZero L] in
/-- If `α` has finite order then so does `α⁻¹`, hence `α ± α⁻¹` is an algebraic integer. -/
lemma isIntegral_inv_of_pow_eq_one {N : ℕ} (hN : N ≠ 0) (h : α ^ N = 1) : IsIntegral ℤ α⁻¹ :=
  isIntegral_of_pow_eq_one hN (by rw [inv_pow, h, inv_one])

/-- **The key structural statement.**  If `α ^ (2 n) = -1` (with `n ≠ 0`) and `-α⁻¹ ≠ α`, then
the ring of integers of `ℚ(α - α⁻¹)` is `ℤ[α - α⁻¹]`. -/
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

variable {L : Type*} [Field L] [CharZero L] [IsAlgClosed L]

/-- A root of the characteristic polynomial `Y ^ 2 - k x Y - t` exists in an algebraically
closed field. -/
private lemma exists_char_root (k t : ℤ) (x : L) :
    ∃ α : L, α ^ 2 - (k : L) * x * α - (t : L) = 0 := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root
    (C (1 : L) * X ^ 2 + C (-((k : L) * x)) * X + C (-(t : L)))
    (by rw [degree_quadratic one_ne_zero]; norm_num)
  refine ⟨α, ?_⟩
  simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hα
  linear_combination hα

variable {k t : ℤ} {n : ℕ} {x α : L}

omit [IsAlgClosed L] in
/-- Under the hypotheses below, `x = α - α⁻¹` and `α ^ (2 n) = -1`. -/
private lemma sub_inv_data (hα : α ^ 2 - ((1 : ℤ) : L) * x * α - ((1 : ℤ) : L) = 0)
    (hne : ((1 : ℤ) : L) * x - α ≠ α) :
    α ≠ 0 ∧ ((1 : ℤ) : L) * x - α = -α⁻¹ ∧ x = α - α⁻¹ ∧ -α⁻¹ ≠ α := by
  have hα0 : α ≠ 0 := char_ne_zero hα one_ne_zero
  have hp := char_prod hα
  have hβ : ((1 : ℤ) : L) * x - α = -α⁻¹ := by
    field_simp
    linear_combination hp
  refine ⟨hα0, hβ, ?_, hβ ▸ hne⟩
  have h := char_sum (k := 1) (x := x) α
  rw [hβ] at h
  simp only [Int.cast_one, one_mul] at h
  rw [← h]; ring

/-- **Theorem 1.1 (Chen–Guo–Hong).**  For `n` odd, the ring of integers of `ℚ(x)` is `ℤ[x]`
for every root `x` of the `n`-th Fibonacci polynomial.  In particular every irreducible
factor of `Fₙ` is monogenic. -/
theorem monogenic_of_isRoot_fibPoly (hn : Odd n) (hx : aeval x (fibPoly 1 1 n) = 0) :
    IsIntegral ℤ x ∧ ∀ y ∈ ℚ⟮x⟯, IsIntegral ℤ y → y ∈ Algebra.adjoin ℤ ({x} : Set L) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨α, hα⟩ := exists_char_root 1 1 x
  have hne := char_ne_of_isRoot_fibPoly hn0 hα one_ne_zero hx
  obtain ⟨hα0, hβ, hxeq, hne'⟩ := sub_inv_data hα hne
  have hp := char_prod hα
  have hbin := aeval_fibPoly (char_sum (k := 1) (x := x) α) hp n
  rw [hx, mul_zero] at hbin
  have h2n : α ^ (2 * n) = -1 := by
    have h1 : α ^ n * α ^ n = α ^ n * (((1 : ℤ) : L) * x - α) ^ n := by
      rw [← sub_eq_zero] at hbin ⊢
      linear_combination -(α ^ n) * hbin
    rw [two_mul, pow_add, h1, ← mul_pow, hp]
    push_cast
    rw [hn.neg_one_pow]
  have h4n : α ^ (4 * n) = 1 := by
    rw [show 4 * n = 2 * n + 2 * n by ring, pow_add, h2n]; ring
  refine ⟨hxeq ▸ (isIntegral_of_pow_eq_one (N := 4 * n) (by omega) h4n).sub
      (isIntegral_inv_of_pow_eq_one (N := 4 * n) (by omega) h4n), fun y hymem hy => ?_⟩
  rw [hxeq] at hymem ⊢
  exact mem_adjoin_int_sub_inv_of_pow_eq_neg_one hn0 h2n hne' hy hymem

/-- **Theorem 1.2 (Chen–Guo–Hong).**  For `n` even and nonzero, the ring of integers of `ℚ(x)`
is `ℤ[x]` for every root `x` of the `n`-th Lucas polynomial. -/
theorem monogenic_of_isRoot_lucasPoly (hn : Even n) (hn0 : n ≠ 0)
    (hx : aeval x (lucasPoly 1 1 n) = 0) :
    IsIntegral ℤ x ∧ ∀ y ∈ ℚ⟮x⟯, IsIntegral ℤ y → y ∈ Algebra.adjoin ℤ ({x} : Set L) := by
  obtain ⟨α, hα⟩ := exists_char_root 1 1 x
  have hne := char_ne_of_isRoot_lucasPoly hα one_ne_zero hx
  obtain ⟨hα0, hβ, hxeq, hne'⟩ := sub_inv_data hα hne
  have hp := char_prod hα
  have hbin := aeval_lucasPoly (char_sum (k := 1) (x := x) α) hp n
  rw [hx] at hbin
  have h2n : α ^ (2 * n) = -1 := by
    have h1 : α ^ n * α ^ n = -(α ^ n * (((1 : ℤ) : L) * x - α) ^ n) := by
      rw [← sub_eq_zero]
      linear_combination α ^ n * hbin.symm
    rw [two_mul, pow_add, h1, ← mul_pow, hp]
    push_cast
    rw [hn.neg_one_pow]
  have h4n : α ^ (4 * n) = 1 := by
    rw [show 4 * n = 2 * n + 2 * n by ring, pow_add, h2n]; ring
  refine ⟨hxeq ▸ (isIntegral_of_pow_eq_one (N := 4 * n) (by omega) h4n).sub
      (isIntegral_inv_of_pow_eq_one (N := 4 * n) (by omega) h4n), fun y hymem hy => ?_⟩
  rw [hxeq] at hymem ⊢
  exact mem_adjoin_int_sub_inv_of_pow_eq_neg_one hn0 h2n hne' hy hymem

omit [IsAlgClosed L] in
/-- Under the hypotheses below, `x = α + α⁻¹` and `α ^ 2 ≠ 1`. -/
private lemma add_inv_data (hα : α ^ 2 - ((1 : ℤ) : L) * x * α - ((-1 : ℤ) : L) = 0)
    (hne : ((1 : ℤ) : L) * x - α ≠ α) :
    α ≠ 0 ∧ ((1 : ℤ) : L) * x - α = α⁻¹ ∧ x = α + α⁻¹ ∧ α ^ 2 ≠ 1 := by
  have hα0 : α ≠ 0 := char_ne_zero hα (by norm_num)
  have hp := char_prod hα
  have hβ : ((1 : ℤ) : L) * x - α = α⁻¹ := by
    field_simp
    push_cast at hp
    linear_combination hp
  refine ⟨hα0, hβ, ?_, ?_⟩
  · have h := char_sum (k := 1) (x := x) α
    rw [hβ] at h
    simp only [Int.cast_one, one_mul] at h
    rw [← h]
  · intro h
    apply hne
    rw [hβ]
    field_simp
    linear_combination -h

/-- **The `t = -1` analogue of Theorem 1.1, valid for every `n ≥ 1`.**  The polynomials
`Fₙ₊₂ = X Fₙ₊₁ - Fₙ` are the Chebyshev polynomials of the second kind; their roots generate
subfields of maximal real subfields of cyclotomic fields, which are monogenic. -/
theorem monogenic_of_isRoot_fibPoly_neg (hn0 : n ≠ 0)
    (hx : aeval x (fibPoly 1 (-1) n) = 0) :
    IsIntegral ℤ x ∧ ∀ y ∈ ℚ⟮x⟯, IsIntegral ℤ y → y ∈ Algebra.adjoin ℤ ({x} : Set L) := by
  obtain ⟨α, hα⟩ := exists_char_root 1 (-1) x
  have hne := char_ne_of_isRoot_fibPoly hn0 hα (by norm_num) hx
  obtain ⟨hα0, hβ, hxeq, hsq⟩ := add_inv_data hα hne
  have hp := char_prod hα
  have hbin := aeval_fibPoly (char_sum (k := 1) (x := x) α) hp n
  rw [hx, mul_zero] at hbin
  have h2n : α ^ (2 * n) = 1 := by
    have h1 : α ^ n * α ^ n = α ^ n * (((1 : ℤ) : L) * x - α) ^ n := by
      rw [← sub_eq_zero] at hbin ⊢
      linear_combination -(α ^ n) * hbin
    rw [two_mul, pow_add, h1, ← mul_pow, hp]
    push_cast
    ring
  refine ⟨hxeq ▸ (isIntegral_of_pow_eq_one (N := 2 * n) (by omega) h2n).add
      (isIntegral_inv_of_pow_eq_one (N := 2 * n) (by omega) h2n), fun y hymem hy => ?_⟩
  rw [hxeq] at hymem ⊢
  exact mem_adjoin_int_add_inv_of_pow_eq_one (by omega) h2n hsq hy hymem

/-- **The `t = -1` analogue of Theorem 1.2, valid for every `n ≥ 1`.**  The polynomials
`Lₙ₊₂ = X Lₙ₊₁ - Lₙ` are (twice) the Chebyshev polynomials of the first kind. -/
theorem monogenic_of_isRoot_lucasPoly_neg (hn0 : n ≠ 0)
    (hx : aeval x (lucasPoly 1 (-1) n) = 0) :
    IsIntegral ℤ x ∧ ∀ y ∈ ℚ⟮x⟯, IsIntegral ℤ y → y ∈ Algebra.adjoin ℤ ({x} : Set L) := by
  obtain ⟨α, hα⟩ := exists_char_root 1 (-1) x
  have hne := char_ne_of_isRoot_lucasPoly hα (by norm_num) hx
  obtain ⟨hα0, hβ, hxeq, hsq⟩ := add_inv_data hα hne
  have hp := char_prod hα
  have hbin := aeval_lucasPoly (char_sum (k := 1) (x := x) α) hp n
  rw [hx] at hbin
  have h2n : α ^ (2 * n) = -1 := by
    have h1 : α ^ n * α ^ n = -(α ^ n * (((1 : ℤ) : L) * x - α) ^ n) := by
      rw [← sub_eq_zero]
      linear_combination α ^ n * hbin.symm
    rw [two_mul, pow_add, h1, ← mul_pow, hp]
    push_cast
    ring
  have h4n : α ^ (4 * n) = 1 := by
    rw [show 4 * n = 2 * n + 2 * n by ring, pow_add, h2n]
    ring
  refine ⟨hxeq ▸ (isIntegral_of_pow_eq_one (N := 4 * n) (by omega) h4n).add
      (isIntegral_inv_of_pow_eq_one (N := 4 * n) (by omega) h4n), fun y hymem hy => ?_⟩
  rw [hxeq] at hymem ⊢
  exact mem_adjoin_int_add_inv_of_pow_eq_one (by omega) h4n hsq hy hymem

/-! ### Reduction of the `(k, t)`-family to the `(1, t)`-family -/

section Comp

variable (k t : ℤ)

/-- The `(k, t)`-Fibonacci polynomials are the `(1, t)`-Fibonacci polynomials rescaled:
`F^{(k,t)}_n(X) = F^{(1,t)}_n(k X)`. -/
lemma fibPoly_eq_comp : ∀ n : ℕ, fibPoly k t n = (fibPoly 1 t n).comp (C k * X)
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [fibPoly_add_two, fibPoly_add_two, add_comp, mul_comp, mul_comp, mul_comp, C_comp, X_comp,
      C_comp, ← fibPoly_eq_comp (n + 1), ← fibPoly_eq_comp n]
    simp

/-- The `(k, t)`-Lucas polynomials are the `(1, t)`-Lucas polynomials rescaled. -/
lemma lucasPoly_eq_comp : ∀ n : ℕ, lucasPoly k t n = (lucasPoly 1 t n).comp (C k * X)
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [lucasPoly_add_two, lucasPoly_add_two, add_comp, mul_comp, mul_comp, mul_comp, C_comp,
      X_comp, C_comp, ← lucasPoly_eq_comp (n + 1), ← lucasPoly_eq_comp n]
    simp

end Comp

/-! ### The full `(k, t)`-generalisation

For every `k`, a root `x` of the `n`-th `(k, t)`-polynomial has `k x` a root of the
corresponding `(1, t)`-polynomial, by `Polynomial.fibPoly_eq_comp`.  Hence `ℚ(k x)` — which
equals `ℚ(x)` whenever `k ≠ 0` — is monogenic under the same hypotheses. -/

section General

variable {k : ℤ}

omit [CharZero L] [IsAlgClosed L] in
private lemma aeval_comp_C_mul_X {p : ℤ[X]} (hx : aeval x (p.comp (C k * X)) = 0) :
    aeval ((k : L) * x) p = 0 := by
  rwa [aeval_comp, map_mul, aeval_C, aeval_X, algebraMap_int_eq, eq_intCast] at hx

/-- **The `(k, 1)`-generalisation of Theorem 1.1.** -/
theorem monogenic_of_isRoot_fibPoly_gen (hn : Odd n) (hx : aeval x (fibPoly k 1 n) = 0) :
    IsIntegral ℤ ((k : L) * x) ∧ ∀ y ∈ ℚ⟮(k : L) * x⟯, IsIntegral ℤ y →
      y ∈ Algebra.adjoin ℤ ({(k : L) * x} : Set L) :=
  monogenic_of_isRoot_fibPoly hn (aeval_comp_C_mul_X (by rwa [← fibPoly_eq_comp]))

/-- **The `(k, 1)`-generalisation of Theorem 1.2.** -/
theorem monogenic_of_isRoot_lucasPoly_gen (hn : Even n) (hn0 : n ≠ 0)
    (hx : aeval x (lucasPoly k 1 n) = 0) :
    IsIntegral ℤ ((k : L) * x) ∧ ∀ y ∈ ℚ⟮(k : L) * x⟯, IsIntegral ℤ y →
      y ∈ Algebra.adjoin ℤ ({(k : L) * x} : Set L) :=
  monogenic_of_isRoot_lucasPoly hn hn0 (aeval_comp_C_mul_X (by rwa [← lucasPoly_eq_comp]))

/-- **The `(k, -1)`-generalisation**, valid for every `n ≥ 1`. -/
theorem monogenic_of_isRoot_fibPoly_neg_gen (hn0 : n ≠ 0)
    (hx : aeval x (fibPoly k (-1) n) = 0) :
    IsIntegral ℤ ((k : L) * x) ∧ ∀ y ∈ ℚ⟮(k : L) * x⟯, IsIntegral ℤ y →
      y ∈ Algebra.adjoin ℤ ({(k : L) * x} : Set L) :=
  monogenic_of_isRoot_fibPoly_neg hn0 (aeval_comp_C_mul_X (by rwa [← fibPoly_eq_comp]))

/-- **The `(k, -1)`-generalisation for Lucas polynomials**, valid for every `n ≥ 1`. -/
theorem monogenic_of_isRoot_lucasPoly_neg_gen (hn0 : n ≠ 0)
    (hx : aeval x (lucasPoly k (-1) n) = 0) :
    IsIntegral ℤ ((k : L) * x) ∧ ∀ y ∈ ℚ⟮(k : L) * x⟯, IsIntegral ℤ y →
      y ∈ Algebra.adjoin ℤ ({(k : L) * x} : Set L) :=
  monogenic_of_isRoot_lucasPoly_neg hn0 (aeval_comp_C_mul_X (by rwa [← lucasPoly_eq_comp]))

end General

/-! ### The theorems in the standard `𝓞 K = ℤ[θ]` form -/

open NumberField in
/-- **Theorem 1.1**, in the form used elsewhere in the monogenity library: the ring of
integers of `ℚ(x)` is generated by `x` for every root `x` of an odd-indexed Fibonacci
polynomial. -/
theorem adjoin_eq_top_of_isRoot_fibPoly (hn : Odd n) (hx : aeval x (fibPoly 1 1 n) = 0) :
    Algebra.adjoin ℤ ({Monogenic.gen (monogenic_of_isRoot_fibPoly hn hx).1} :
      Set (𝓞 ℚ⟮x⟯)) = ⊤ :=
  Monogenic.adjoin_eq_top_of_forall_mem _ (monogenic_of_isRoot_fibPoly hn hx).2

open NumberField in
/-- **Theorem 1.2**, in the form used elsewhere in the monogenity library. -/
theorem adjoin_eq_top_of_isRoot_lucasPoly (hn : Even n) (hn0 : n ≠ 0)
    (hx : aeval x (lucasPoly 1 1 n) = 0) :
    Algebra.adjoin ℤ ({Monogenic.gen (monogenic_of_isRoot_lucasPoly hn hn0 hx).1} :
      Set (𝓞 ℚ⟮x⟯)) = ⊤ :=
  Monogenic.adjoin_eq_top_of_forall_mem _ (monogenic_of_isRoot_lucasPoly hn hn0 hx).2

open NumberField in
/-- The `t = -1` Fibonacci (Chebyshev) analogue, in the standard form. -/
theorem adjoin_eq_top_of_isRoot_fibPoly_neg (hn0 : n ≠ 0)
    (hx : aeval x (fibPoly 1 (-1) n) = 0) :
    Algebra.adjoin ℤ ({Monogenic.gen (monogenic_of_isRoot_fibPoly_neg hn0 hx).1} :
      Set (𝓞 ℚ⟮x⟯)) = ⊤ :=
  Monogenic.adjoin_eq_top_of_forall_mem _ (monogenic_of_isRoot_fibPoly_neg hn0 hx).2

open NumberField in
/-- The `t = -1` Lucas (Chebyshev) analogue, in the standard form. -/
theorem adjoin_eq_top_of_isRoot_lucasPoly_neg (hn0 : n ≠ 0)
    (hx : aeval x (lucasPoly 1 (-1) n) = 0) :
    Algebra.adjoin ℤ ({Monogenic.gen (monogenic_of_isRoot_lucasPoly_neg hn0 hx).1} :
      Set (𝓞 ℚ⟮x⟯)) = ⊤ :=
  Monogenic.adjoin_eq_top_of_forall_mem _ (monogenic_of_isRoot_lucasPoly_neg hn0 hx).2

end Main

end Polynomial

end

end
