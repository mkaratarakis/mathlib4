/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Linear independence of exponential polynomials

Polynomials times exponentials with distinct frequencies are linearly independent: if
`∑_c Q_c (ζ) e ^ {c ζ} = 0` for all `ζ ∈ ℂ`, with distinct `c`, then every `Q_c` is zero.  In
several variables the same holds for `∑_w P_w (z) e ^ {w · z}`, by restricting to a line on
which the frequencies stay distinct and the polynomials stay nonzero.

This is what makes the auxiliary function of the Schneider–Lang criterion nonzero.

## Main statements

* `ExpPoly.eq_zero_of_sum_eval_mul_cexp`: one variable.
* `ExpPoly.eq_zero_of_sum_eval_mul_cexp_pi`: several variables.
-/

@[expose] public section

open Polynomial Finset

namespace ExpPoly

/-- The size of a family of polynomials: the sum over its nonzero members of `natDegree + 1`. -/
noncomputable def size (T : Finset ℂ) (Q : ℂ → ℂ[X]) : ℕ :=
  ∑ c ∈ T, if Q c = 0 then 0 else (Q c).natDegree + 1

lemma derivative_add_C_mul {Q : ℂ[X]} (hQ : Q ≠ 0) {a : ℂ} (ha : a ≠ 0) :
    derivative Q + C a * Q ≠ 0 ∧ (derivative Q + C a * Q).natDegree = Q.natDegree := by
  set d := Q.natDegree with hd
  have hcoeff : (derivative Q + C a * Q).coeff d = a * Q.leadingCoeff := by
    rw [coeff_add, coeff_derivative, coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < d + 1), zero_mul, zero_add]
    rfl
  have hne : (derivative Q + C a * Q).coeff d ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero ha (leadingCoeff_ne_zero.2 hQ)
  have hle : (derivative Q + C a * Q).natDegree ≤ d :=
    natDegree_add_le_of_degree_le ((natDegree_derivative_le Q).trans (by omega))
      (natDegree_C_mul_le a Q)
  exact ⟨fun h => hne (by rw [h, coeff_zero]), le_antisymm hle (le_natDegree_of_ne_zero hne)⟩

/-- **Exponential polynomials in one variable.**  If `∑_{c ∈ T} Q_c (ζ) e ^ {c ζ} = 0` for all
`ζ`, then every `Q_c` is zero. -/
theorem eq_zero_of_sum_eval_mul_cexp (T : Finset ℂ) (Q : ℂ → ℂ[X])
    (hQ : ∀ ζ : ℂ, ∑ c ∈ T, (Q c).eval ζ * Complex.exp (c * ζ) = 0) : ∀ c ∈ T, Q c = 0 := by
  suffices key : ∀ (N : ℕ) (Q : ℂ → ℂ[X]), size T Q ≤ N →
      (∀ ζ : ℂ, ∑ c ∈ T, (Q c).eval ζ * Complex.exp (c * ζ) = 0) → ∀ c ∈ T, Q c = 0 from
    key _ Q le_rfl hQ
  intro N
  induction N with
  | zero =>
    intro Q hs _ c hc
    by_contra h
    have := Finset.single_le_sum (f := fun c => if Q c = 0 then 0 else (Q c).natDegree + 1)
      (fun _ _ => Nat.zero_le _) hc
    simp only [h, ↓reduceIte] at this
    unfold size at hs
    omega
  | succ N ih =>
    intro Q hs hQ
    by_contra hall
    push Not at hall
    obtain ⟨c₀, hc₀, hQc₀⟩ := hall
    set Q' : ℂ → ℂ[X] := fun c => derivative (Q c) + C (c - c₀) * Q c with hQ'
    -- the new family is again a vanishing combination
    have hid' : ∀ ζ : ℂ, ∑ c ∈ T, (Q' c).eval ζ * Complex.exp (c * ζ) = 0 := by
      intro ζ
      set G : ℂ → ℂ := fun ζ => ∑ c ∈ T, (Q c).eval ζ * Complex.exp ((c - c₀) * ζ) with hG
      have hG0 : G = fun _ => 0 := by
        funext ζ
        have h := hQ ζ
        have : G ζ = Complex.exp (-c₀ * ζ) * ∑ c ∈ T, (Q c).eval ζ * Complex.exp (c * ζ) := by
          rw [hG, Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [show (c - c₀) * ζ = -c₀ * ζ + c * ζ by ring, Complex.exp_add]
          ring
        rw [this, h, mul_zero]
      have hderiv : HasDerivAt G (∑ c ∈ T, ((derivative (Q c)).eval ζ *
          Complex.exp ((c - c₀) * ζ) + (Q c).eval ζ *
            ((c - c₀) * Complex.exp ((c - c₀) * ζ)))) ζ := by
        refine HasDerivAt.fun_sum fun c _ => ?_
        refine ((Q c).hasDerivAt ζ).mul ?_
        have := ((hasDerivAt_id ζ).const_mul (c - c₀)).cexp
        simpa [mul_comm] using this
      rw [hG0] at hderiv
      have h0 := hderiv.unique (hasDerivAt_const ζ (0 : ℂ))
      have : ∑ c ∈ T, (Q' c).eval ζ * Complex.exp (c * ζ) = Complex.exp (c₀ * ζ) *
          ∑ c ∈ T, ((derivative (Q c)).eval ζ * Complex.exp ((c - c₀) * ζ) +
            (Q c).eval ζ * ((c - c₀) * Complex.exp ((c - c₀) * ζ))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [hQ', eval_add, eval_mul, eval_C]
        rw [show c * ζ = c₀ * ζ + (c - c₀) * ζ by ring, Complex.exp_add]
        ring
      rw [this, h0, mul_zero]
    -- and it is smaller
    have hsize : size T Q' < size T Q := by
      refine Finset.sum_lt_sum (fun c hc => ?_) ⟨c₀, hc₀, ?_⟩
      · by_cases hcc : c = c₀
        · subst hcc
          simp only [hQ', sub_self, map_zero, zero_mul, add_zero, hQc₀, ↓reduceIte]
          by_cases hd : derivative (Q c) = 0
          · simp [hd]
          · simp only [hd, ↓reduceIte]
            have hdeg : (Q c).natDegree ≠ 0 := fun h0 => hd (derivative_of_natDegree_zero h0)
            have := natDegree_derivative_lt hdeg
            omega
        · by_cases hQc : Q c = 0
          · simp [hQ', hQc]
          · obtain ⟨hne, hdeg⟩ := derivative_add_C_mul hQc (sub_ne_zero.2 hcc)
            simp only [hQ', hne, hQc, ↓reduceIte, hdeg, le_refl]
      · simp only [hQ', sub_self, map_zero, zero_mul, add_zero, hQc₀, ↓reduceIte]
        by_cases hd : derivative (Q c₀) = 0
        · simp [hd]
        · simp only [hd, ↓reduceIte]
          have hdeg : (Q c₀).natDegree ≠ 0 := fun h0 => hd (derivative_of_natDegree_zero h0)
          have := natDegree_derivative_lt hdeg
          omega
    have hQ'0 := ih Q' (by omega) hid'
    -- recover `Q`
    have hne : ∀ c ∈ T, c ≠ c₀ → Q c = 0 := fun c hc hcc => by
      by_contra h
      exact (derivative_add_C_mul h (sub_ne_zero.2 hcc)).1 (hQ'0 c hc)
    have hd0 : derivative (Q c₀) = 0 := by simpa [hQ'] using hQ'0 c₀ hc₀
    have hconst : Q c₀ = C ((Q c₀).coeff 0) :=
      eq_C_of_natDegree_eq_zero (derivative_eq_zero.1 hd0)
    have h0 := hQ 0
    rw [Finset.sum_eq_single c₀ (fun c hc hcc => by rw [hne c hc hcc, eval_zero, zero_mul])
      (fun h => absurd hc₀ h), hconst, eval_C, mul_zero, Complex.exp_zero, mul_one] at h0
    exact hQc₀ (by rw [hconst, h0, map_zero])

end ExpPoly
