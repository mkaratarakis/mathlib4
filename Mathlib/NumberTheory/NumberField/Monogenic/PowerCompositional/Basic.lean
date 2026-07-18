/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.NumberField.Monogenic.PowerCompositional.Ideal
public import Mathlib.NumberTheory.NumberField.Monogenic.Pure

/-!
# Square divisors of the constant term obstruct monogenicity

This file proves Proposition 2.3 of S. Kaur, S. Kumar and L. Remete,
*On the index of power compositional polynomials*,
Finite Fields Appl. **107** (2025), 102642: if `p ^ 2` divides `f(0)` then `p` divides the
index of `f(X ^ ℓ)` for every `ℓ > 1`.

This is the obstruction that forces condition (3) — squarefreeness of `f(0)` — in the
paper's Theorem 1.1.

The proof needs only the *necessity* half of Dedekind's criterion, available here as
`RingOfIntegers.dvd_exponent_of_sq_factor`, whose hypothesis
`minpoly = h ^ 2 * g + p * (k * h) + p ^ 2 * t` is precisely membership of the minimal
polynomial in `⟨p, h⟩ ^ 2`.  Taking `h = X`, the required decomposition of `f(X ^ ℓ)` is
immediate: all of its nonconstant terms carry a factor `X ^ ℓ`, hence a factor `X ^ 2`
since `ℓ ≥ 2`, and the constant term is `f(0)`, divisible by `p ^ 2` by hypothesis.

## Main results

* `RingOfIntegers.dvd_exponent_of_sq_dvd_coeff_zero`: Proposition 2.3.

* `RingOfIntegers.sq_not_dvd_coeff_zero_of_adjoin_eq_top`: its contrapositive, which is the
  necessity of condition (3) of Theorem 1.1.

## References

* [S. Kaur, S. Kumar, L. Remete, *On the index of power compositional polynomials*][KKR2025]
-/

@[expose] public section

noncomputable section

open Polynomial NumberField

namespace RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}
variable {p : ℕ} [hp : Fact p.Prime]

/-- **Proposition 2.3** of Kaur–Kumar–Remete.  If `p ^ 2` divides the constant term of a
monic `f : ℤ[X]`, and `θ` is a root of `f(X ^ ℓ)` with `ℓ ≥ 2`, then `p` divides the index
`[𝓞 K : ℤ[θ]]`.

Consequently a monogenic power-compositional polynomial `f(X ^ ℓ)` must have `f(0)`
squarefree, which is condition (3) of the paper's Theorem 1.1. -/
theorem dvd_exponent_of_sq_dvd_coeff_zero {f : ℤ[X]} (hf : f.Monic) {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (hp2 : (p : ℤ) ^ 2 ∣ f.coeff 0) (hmin : minpoly ℤ θ = expand ℤ ℓ f) :
    p ∣ exponent θ := by
  have hℓ0 : 0 < ℓ := by omega
  set F := expand ℤ ℓ f with hFdef
  have hFm : F.Monic := hf.expand hℓ0
  -- `f` is nonconstant: otherwise `f = 1` and `p ^ 2 ∣ 1`.
  have hfd : 0 < f.natDegree := by
    rcases Nat.eq_zero_or_pos f.natDegree with h0 | h
    · exfalso
      rw [hf.natDegree_eq_zero.mp h0] at hp2
      have h1 : (p : ℤ) ^ 2 ∣ 1 := by simpa using hp2
      have hle : (p : ℤ) ^ 2 ≤ 1 := Int.le_of_dvd one_pos h1
      have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.out.two_le
      nlinarith
    · exact h
  have hFd : 0 < F.natDegree := by
    rw [hFdef, natDegree_expand]
    positivity
  -- The constant term of `f(X ^ ℓ)` is `f(0)`.
  have hF0 : F.coeff 0 = f.coeff 0 := by
    rw [hFdef, coeff_expand hℓ0]
    simp
  -- Every other low-order coefficient vanishes, so `X ^ 2` divides `F - C (F.coeff 0)`.
  obtain ⟨G, hG⟩ : (X : ℤ[X]) ^ 2 ∣ F - C (F.coeff 0) := by
    rw [X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · simp
    · rw [coeff_sub, coeff_C, hFdef, coeff_expand hℓ0]
      simp [Nat.dvd_one.not.mpr (by omega : ℓ ≠ 1)]
  -- `X ^ 2 * G` is monic of the same degree as `F`, hence so is `X * G` one degree lower.
  have hdegC : (C (F.coeff 0)).degree < F.degree :=
    lt_of_le_of_lt degree_C_le (natDegree_pos_iff_degree_pos.mp hFd)
  have hXG2 : ((X : ℤ[X]) ^ 2 * G).Monic := hG ▸ hFm.sub_of_left hdegC
  have hXG : ((X : ℤ[X]) * G).Monic := by
    refine monic_X.of_mul_monic_left ?_
    rw [show (X : ℤ[X]) * ((X : ℤ[X]) * G) = X ^ 2 * G by ring]
    exact hXG2
  have hG0 : G ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hXG2
    exact not_monic_zero hXG2
  -- Degree bookkeeping.
  have hnd : ((X : ℤ[X]) * G).natDegree < F.natDegree := by
    have h2 : ((X : ℤ[X]) ^ 2 * G).natDegree = F.natDegree := by
      rw [← hG, natDegree_sub_C]
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hG0, natDegree_X_pow] at h2
    rw [natDegree_mul X_ne_zero hG0, natDegree_X]
    omega
  -- Assemble the decomposition witnessing `minpoly ∈ ⟨p, X⟩ ^ 2`.
  obtain ⟨c, hc⟩ := hp2
  refine dvd_exponent_of_sq_factor (h := X) (g := G) (k := 0) (t := C c) hXG
    (by rw [hmin]; exact hnd) ?_
  have hCF0 : C (F.coeff 0) = C (p : ℤ) ^ 2 * C c := by
    rw [hF0, hc, map_mul, map_pow]
  rw [hmin, ← hCF0]
  linear_combination hG

/-- Condition (3) of the paper's Theorem 1.1 is necessary: if `f(X ^ ℓ)` is monogenic with
`ℓ ≥ 2`, then no rational prime square divides `f(0)`.

This is the contrapositive of `dvd_exponent_of_sq_dvd_coeff_zero`.  Quantifying over `p`
turns it into squarefreeness of `f(0)`. -/
theorem sq_not_dvd_coeff_zero_of_adjoin_eq_top {f : ℤ[X]} (hf : f.Monic) {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (hmin : minpoly ℤ θ = expand ℤ ℓ f) (htop : Algebra.adjoin ℤ {θ} = ⊤) :
    ¬ (p : ℤ) ^ 2 ∣ f.coeff 0 := fun hp2 => by
  have hdvd := dvd_exponent_of_sq_dvd_coeff_zero hf hℓ hp2 hmin
  rw [← exponent_eq_one_iff] at htop
  exact hp.out.one_lt.ne' (Nat.dvd_one.mp (htop ▸ hdvd))

end RingOfIntegers
